{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

module Rattus.Plugin.ScopeCheck (checkAll) where

import Rattus.Plugin.Utils
import Rattus.Plugin.Dependency
import Rattus.Plugin.Annotation

import Prelude hiding ((<>))
-- import Outputable
import GhcPlugins
import TcRnTypes
import Bag
import HsExtension
import HsExpr
import HsBinds
import Data.Graph
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)
import System.Exit
import Data.Maybe

import Control.Monad

data Ctxt = Ctxt
  { current :: LCtxt,
    hidden :: Hidden,
    hiddenRec :: Hidden,
    earlier :: Maybe LCtxt,
    srcLoc :: SrcSpan,
    recDef :: Maybe RecDef,
    stableTypes :: Set Var,
    primAlias :: Map Var Prim,
    stabilized :: Bool}
         
emptyCtxt :: Maybe (Set Var,SrcSpan) -> Ctxt
emptyCtxt mvar =
  Ctxt { current =  Set.empty,
        earlier = Nothing,
        hidden = Map.empty,
        hiddenRec = Map.empty,
        srcLoc = UnhelpfulSpan "<no location info>",
        recDef = mvar,
        primAlias = Map.empty,
        stableTypes = Set.empty,
        stabilized = isJust mvar}

type LCtxt = Set Var

type RecDef = (Set Var, SrcSpan) -- the recursively defined variables + the position where the recursive definition starts
data HiddenReason = NestedRec SrcSpan -- | FunDef | BoxApp | AdvApp
type Hidden = Map Var HiddenReason
data Prim  -- = Delay | Adv | Box | Unbox | Arr

  
type GetCtxt = ?ctxt :: Ctxt

class Scope a where
  check :: GetCtxt => a -> TcM Bool

-- Check scope for things that also can bind variables. To this end
-- the 'checkBind' function returns the updated context with the bound
-- variables added.
class ScopeBind a where
  checkBind :: GetCtxt => a -> TcM (Bool,Ctxt)


setCtxt :: Ctxt -> (GetCtxt => a) -> a 
setCtxt c a = let ?ctxt = c in a

modifyCtxt :: (Ctxt -> Ctxt) -> (GetCtxt => a) -> (GetCtxt => a)
modifyCtxt f a = let ?ctxt = f ?ctxt in a


checkAll :: TcGblEnv -> TcM ()
checkAll env = do
  let bindDep = filter (filterBinds (tcg_mod env) (tcg_ann_env env)) (dependency (tcg_binds env))
  mapM_ printBinds bindDep
  res <- mapM checkSCC bindDep
  if and res then return () else liftIO exitFailure


filterBinds :: Module -> AnnEnv -> SCC (LHsBindLR  GhcTc GhcTc, Set Var) -> Bool
filterBinds mod anEnv scc =
  case scc of
    (AcyclicSCC (_,vs)) -> any checkVar vs
    (CyclicSCC bs) -> any (any checkVar . snd) bs
  where checkVar :: Var -> Bool
        checkVar v =
          let anns = findAnns deserializeWithData anEnv (NamedTarget name) :: [Rattus]
              annsMod = findAnns deserializeWithData anEnv (ModuleTarget mod) :: [Rattus]
              name :: Name
              name = varName v
          in Rattus `elem` anns || (not (NotRattus `elem` anns)  && Rattus `elem` annsMod)


instance Scope a => Scope (GenLocated SrcSpan a) where
  check (L l x) =  (\c -> c {srcLoc = l}) `modifyCtxt` check x


instance Scope (LHsBinds GhcTc) where
  check bs = fmap and (mapM check (bagToList bs))

instance Scope a => Scope [a] where
  check ls = fmap and (mapM check ls)


instance Scope (Match GhcTc (LHsExpr GhcTc)) where
  check Match{m_pats=ps,m_grhss=rhs} = addVars (getBV ps) `modifyCtxt` check rhs
  check XMatch{} = return True

instance Scope (MatchGroup GhcTc (LHsExpr GhcTc)) where
  check MG {mg_alts = alts} = check alts
  check XMatchGroup {} = return True

instance ScopeBind (StmtLR GhcTc GhcTc (LHsExpr GhcTc)) where
  checkBind (LastStmt _ b _ _) =  ( , ?ctxt) <$> check b
  checkBind (BindStmt _ p b _ _) = do
    let c' = addVars (getBV p) ?ctxt
    r <- setCtxt c' (check b)
    return (r,c')
  checkBind (BodyStmt _ b _ _) = ( , ?ctxt) <$> check b
  checkBind (LetStmt _ bs) = checkBind bs
  checkBind ParStmt{} = return (True,?ctxt) -- TODO: warning that monad comprehension is not supported
  checkBind TransStmt{} = return (True,?ctxt) -- TODO: warning that monad comprehension is not supported
  checkBind ApplicativeStmt{} = return (True,?ctxt) -- TODO: warning that applicative do notation is not supported
  checkBind RecStmt{} = return (True,?ctxt) -- TODO: warning that recursive do notation is not supported
  checkBind XStmtLR {} = return (True,?ctxt)


instance ScopeBind a => ScopeBind [a] where
  checkBind [] = return (True,?ctxt)
  checkBind (x:xs) = do
    (r,c) <- checkBind x
    (r',c') <- setCtxt c (checkBind xs)
    return (r && r',c')

instance ScopeBind a => ScopeBind (GenLocated SrcSpan a) where
  checkBind (L l x) =  (\c -> c {srcLoc = l}) `modifyCtxt` checkBind x


instance Scope (GRHS GhcTc (LHsExpr GhcTc)) where
  check (GRHS _ gs b) = do
    (r, c) <- checkBind gs
    r' <- setCtxt c (check b)
    return (r && r')
  check XGRHS{} = return True

instance ScopeBind (SCC (LHsBindLR GhcTc GhcTc, Set Var)) where
  checkBind (AcyclicSCC (b,vs)) = (, addVars vs ?ctxt) <$> check b
  checkBind (CyclicSCC bs) = do
    res <- fmap and (mapM check' bs')
    when (res && stabilized ?ctxt) 
      (printMessage' SevWarning
        (text "recursive definition nested inside a box or annother recursive definition can cause time leaks"))
    return (res, addVars vs ?ctxt)
    where bs' = map fst bs
          vs = foldMap snd bs
          check' b@(L l _) = fc l `modifyCtxt` check b
          fc l c = let
            ctxHid = maybe (current c) (Set.union (current c)) (earlier c)
            recHid = maybe ctxHid (Set.union ctxHid . fst) (recDef c)
            in c {current = Set.empty,
                  earlier = Nothing,
                  hidden =  hidden c `Map.union`
                            (Map.fromSet (const (NestedRec l)) recHid),
                  recDef = Just (vs,l),
                  stabilized = True}

instance ScopeBind (HsValBindsLR GhcTc GhcTc) where
  checkBind (ValBinds _ bs _) = checkBind (dependency bs)
  
  checkBind XValBindsLR{} = return (True,?ctxt)

instance ScopeBind (HsLocalBindsLR GhcTc GhcTc) where
  checkBind (HsValBinds _ bs) = checkBind bs
  checkBind HsIPBinds {} = return (True,?ctxt) -- TODO: issue warning that IP are not supported
  checkBind EmptyLocalBinds{} = return (True,?ctxt)
  checkBind XHsLocalBindsLR{} = return (True,?ctxt)

instance Scope (GRHSs GhcTc (LHsExpr GhcTc)) where
  check GRHSs{grhssGRHSs = rhs, grhssLocalBinds = lbinds} = do
    (l,c) <- checkBind lbinds
    r <- setCtxt c (check rhs)
    return (r && l)
  check XGRHSs{} = return True

instance Scope (HsExpr GhcTc) where
  check = undefined

instance Scope (HsBindLR GhcTc GhcTc) where
  check AbsBinds {abs_binds = binds} = check binds
  check FunBind{fun_matches= matches} = check matches
  check PatBind{pat_lhs = lhs, pat_rhs=rhs} =  addVars (getBV lhs) `modifyCtxt` check rhs
  check VarBind{var_rhs = rhs} = check rhs
  check PatSynBind {} = return True -- TODO: show warning that pattern synonyms are not supported
  check XHsBindsLR {} = return True

checkSCC :: SCC (LHsBindLR  GhcTc GhcTc, Set Var) -> TcM Bool
checkSCC (AcyclicSCC (b,_)) = setCtxt (emptyCtxt Nothing) (check b)
checkSCC (CyclicSCC bs) = (fmap and (mapM check' bs'))
  where bs' = map fst bs
        vs = foldMap snd bs
        check' b@(L l _) = setCtxt (emptyCtxt (Just (vs,l))) (check b)


addVars :: Set Var -> Ctxt -> Ctxt
addVars vs c = c{current = vs `Set.union` current c }



printMessage' :: GetCtxt => Severity -> SDoc ->  TcM ()
printMessage' sev doc = printMessage sev (srcLoc ?ctxt) doc
