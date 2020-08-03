{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

module Rattus.Plugin.ScopeCheck (checkAll) where

-- import Rattus.Plugin.Utils
import Rattus.Plugin.Dependency
import Rattus.Plugin.Annotation

import Prelude hiding ((<>))
-- import Outputable
import GhcPlugins
import TcRnTypes
-- import Bag
import HsExtension
-- import HsExpr
import HsBinds
import Data.Graph
-- import qualified Data.Set as Set
import Data.Set (Set)
import System.Exit




data Ctx = Ctx
  { recDef :: Maybe RecDef,
    srcLoc :: SrcSpan}

  -- current :: LCtx,
  --   hidden :: Hidden,
  --   earlier :: Maybe LCtx,
  --   srcLoc :: SrcSpan,
  --   recDef :: Maybe RecDef,
  --   hiddenRecs :: Set Var,
  --   stableTypes :: Set Var,
  --   primAlias :: Map Var Prim,
  --   stabilized :: Bool}

-- type LCtx = Set Var
-- type Hidden = Set Var
type RecDef = Set Var

-- data Prim = Delay | Adv | Box | Unbox | Arr

  
type GetCtx = ?ctx :: Ctx

class Scope a where
  check :: GetCtx => a -> TcM Bool



-- checkGRHSs :: Monad m => GRHSs p body -> m ()
-- checkGRHSs GRHSs {grhssGRHSs = grhss, grhssLocalBinds = lbinds} = return ()

-- checkMatch :: (GetCtx, Monad m) => GenLocated l (Match p body) -> m ()
-- checkMatch (L _lm (Match {m_pats = pats, m_grhss = rhs})) =
--   checkGRHSs rhs
-- checkMatch _ = return () -- TODO: do we need to check other matches? Probably not.


-- checkFunction :: (GetCtx, Monad m) => MatchGroup p body -> m ()
-- checkFunction MG{mg_alts = L _lm matches} = mapM_ checkMatch matches
-- checkFunction _ = return () -- TODO: do we need to check other bindings?

setCtx :: Ctx -> (GetCtx => a) -> a 
setCtx c a = let ?ctx = c in a

modifyCtx :: (Ctx -> Ctx) -> (GetCtx => a) -> (GetCtx => a)
modifyCtx f a = let ?ctx = f ?ctx in a


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
  check (L l x) =  (\c -> c {srcLoc = l}) `modifyCtx` (check x)


instance Scope (HsBindLR GhcTc GhcTc) where
  check _ = return True -- TODO: implement

checkSCC :: SCC (LHsBindLR  GhcTc GhcTc, Set Var) -> TcM Bool
checkSCC (AcyclicSCC (b,_)) = setCtx (Ctx {recDef = Nothing, srcLoc = UnhelpfulSpan "<no location info>"}) (check b)
checkSCC (CyclicSCC bs) = setCtx (Ctx {recDef = Just vs, srcLoc = UnhelpfulSpan "<no location info>"}) (fmap and (mapM check bs'))
  where bs' = map fst bs
        vs = foldMap snd bs


-- checkBind :: GetCtx => LHsBindLR  GhcTc GhcTc -> TcM ()

-- checkBind b@(L _l FunBind{fun_id = (L _idl id),fun_matches= matches}) = checkFunction matches
-- checkBind (L l (AbsBinds {abs_binds = binds})) = do

--   foldBag (>>) checkBind (return ()) binds
-- checkBind (L _ _) = return () -- TODO: do we need to check other kinds of bindings? Yes


-- printMessage :: Severity -> SrcSpan -> SDoc ->  TcM ()
-- printMessage sev l doc = do
--   dflags <- getDynFlags
--   -- let sty = case sev of
--   --                    SevError   -> defaultErrStyle dflags
--   --                    SevWarning -> err_sty
--   --                    _ -> defaultUserStyle dflags
--   --                    -- -> defaultDumpStyle dflags
--   liftIO $ putLogMsg dflags NoReason sev l (defaultErrStyle dflags) doc
