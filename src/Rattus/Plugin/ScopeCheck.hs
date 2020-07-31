{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Rattus.Plugin.ScopeCheck (checkAll) where

import Rattus.Plugin.Utils 
import Rattus.Plugin.Annotation

import Prelude hiding ((<>))
import Outputable
import GhcPlugins
import TcRnTypes
import Bag
import HsExtension
import HsExpr
import HsTypes
import HsPat
import HsBinds
import Data.Set (Set)
import qualified Data.Set as Set

-- import Data.Map (Map)
-- import qualified Data.Map as Map
-- import Data.Maybe

-- import System.Exit


checkAll :: TcGblEnv -> TcM ()
checkAll env = foldBag (>>) (checkBind (tcg_mod env) (tcg_ann_env env)) (return ()) (tcg_binds env)


-- | Return all variables bound by the given list of patterns.
getPatsVars :: [Pat GhcTc] -> Set Var
getPatsVars ps = foldl (\s p -> getPatVars p `Set.union` s) Set.empty ps

-- | Return all variables bound by the given pattern.
conPatVars (PrefixCon ps) = getPatsVars ps
conPatVars (InfixCon p p') = getPatVars p `Set.union` getPatVars p'
conPatVars (RecCon (HsRecFields {rec_flds = fs})) = foldl run Set.empty fs
      where run s (L _ f) = getPatVars (hsRecFieldArg f) `Set.union` s
getPatVars :: Pat GhcTc -> Set Var
getPatVars (VarPat _ (L _ v)) = Set.singleton v
getPatVars (LazyPat _ p) = getPatVars p
getPatVars (AsPat _ (L _ v) p) = Set.insert v (getPatVars p)
getPatVars (ParPat _ p) = getPatVars p
getPatVars (BangPat _ p) = getPatVars p
getPatVars (ListPat _ ps) = getPatsVars ps
getPatVars (TuplePat _ ps _) = getPatsVars ps
getPatVars (SumPat _ p _ _) = getPatVars p
getPatVars (ConPatIn (L _ v) con) = Set.insert v (conPatVars con)
getPatVars (ConPatOut {pat_args = con}) = conPatVars con
getPatVars (ViewPat _ _ p) = getPatVars p
getPatVars (SplicePat _ sp) =
  case sp of
    HsTypedSplice _ _ v _ -> Set.singleton v
    HsUntypedSplice _ _ v _ ->  Set.singleton v
    HsQuasiQuote _ p p' _ _ -> Set.fromList [p,p']
    HsSpliced _ _ (HsSplicedPat p) -> getPatVars p
    _ -> Set.empty
getPatVars (NPlusKPat _ (L _ v) _ _ _ _) = Set.singleton v
getPatVars (SigPat _ p _) = getPatVars p
getPatVars (CoPat _ _ p _) = getPatVars p
getPatVars (NPat {}) = Set.empty
getPatVars (XPat {}) = Set.empty
getPatVars (WildPat {}) = Set.empty
getPatVars (LitPat {}) = Set.empty


checkMatch :: Monad m => GenLocated l (Match p body) -> m ()
checkMatch (L lm (Match {m_pats = pats, m_grhss = rhs})) =
  return ()
checkMatch _ = return ()


checkFunction :: Monad m => MatchGroup p body -> m ()
checkFunction MG{mg_alts = L lm matches} = mapM_ checkMatch matches
checkFunction _ = return () -- TODO: do we need to check other bindings?

checkBind :: Module -> AnnEnv -> LHsBindLR  GhcTc GhcTc -> TcM ()
-- check a function binding (consisting of matches)
checkBind mod anEnv (L l FunBind{fun_id = (L idl id),fun_matches= matches}) =
  if isRattus then checkFunction matches else return ()
  where
    isRattus = Rattus `elem` anns || (not (NotRattus `elem` anns)  && Rattus `elem` annsMod)
    anns = findAnns deserializeWithData anEnv (NamedTarget name) :: [Rattus]
    annsMod = findAnns deserializeWithData anEnv (ModuleTarget mod) :: [Rattus]
    name :: Name
    name = varName id
-- check a bag of bindings
checkBind mod anEnv (L l (AbsBinds {abs_binds = binds})) =
  foldBag (>>) (checkBind mod anEnv) (return ()) binds

checkBind _ _ (L l _) = return () -- TODO: do we need to check other kinds of bindings?


printMessage :: Severity -> SrcSpan -> SDoc ->  TcM ()
printMessage sev l doc = do
  dflags <- getDynFlags
  -- let sty = case sev of
  --                    SevError   -> defaultErrStyle dflags
  --                    SevWarning -> err_sty
  --                    _ -> defaultUserStyle dflags
  --                    -- -> defaultDumpStyle dflags
  liftIO $ putLogMsg dflags NoReason sev l (defaultErrStyle dflags) doc
