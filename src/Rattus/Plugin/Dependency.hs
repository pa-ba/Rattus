{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}

-- | This module is used to perform a dependency analysis of top-level
-- function definitions, i.e. to find out which defintions are
-- (mutual) recursive. To this end, this module also provides a
-- functions to compute, bound variables and variable occurrences.

module Rattus.Plugin.Dependency (dependency, HasBV (..)) where


import GhcPlugins
import Bag


#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Extension
import GHC.Hs.Expr
import GHC.Hs.Pat
import GHC.Hs.Binds
import GHC.Hs.Types
#else 
import HsExtension
import HsExpr
import HsPat
import HsBinds
import HsTypes
#endif

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Graph
import Data.Maybe
import Data.Either
import Prelude hiding ((<>))





-- | Compute the dependencies of a bag of bindings, returning a list
-- of the strongly-connected components.
dependency :: Bag (LHsBindLR GhcTc GhcTc) -> [SCC (LHsBindLR GhcTc GhcTc, Set Var)]
dependency binds = map AcyclicSCC noDeps ++ catMaybes (map filterJust (stronglyConnComp (concat deps)))
  where (deps,noDeps) = partitionEithers $ map mkDep $ bagToList binds
        mkDep :: GenLocated l (HsBindLR GhcTc GhcTc) ->
                 Either [(Maybe (GenLocated l (HsBindLR GhcTc GhcTc), Set Var), Name, [Name])]
                 (GenLocated l (HsBindLR GhcTc GhcTc), Set Var)
        mkDep b =
          let dep = map varName $ Set.toList (getFV b)
              vars = getBV b in
          case Set.toList vars of
            (v:vs) -> Left ((Just (b,vars), varName v , dep) : map (\ v' -> (Nothing, varName v' , dep)) vs)
            [] -> Right (b,vars)
        filterJust (AcyclicSCC Nothing) = Nothing -- this should not happen
        filterJust (AcyclicSCC (Just b)) = Just (AcyclicSCC b)
        filterJust (CyclicSCC bs) = Just (CyclicSCC (catMaybes bs))


-- printBinds (AcyclicSCC bind) = liftIO (putStr "acyclic bind: ") >> printBind (fst bind) >> liftIO (putStrLn "") 
-- printBinds (CyclicSCC binds) = liftIO (putStr "cyclic binds: ") >> mapM_ (printBind . fst) binds >> liftIO (putStrLn "") 


-- printBind (L _ FunBind{fun_id = L _ name}) = 
--   liftIO $ putStr $ (getOccString name ++ " ")
-- printBind (L _ (AbsBinds {abs_exports = exp})) = 
--   mapM_ (\ e -> liftIO $ putStr $ ((getOccString $ abe_poly e)  ++ " ")) exp
-- printBind (L _ (VarBind {var_id = name})) =   liftIO $ putStr $ (getOccString name ++ " ")
-- printBind _ = return ()

-- | Computes the variables that are bound by a given piece of syntax.

class HasBV a where
  getBV :: a -> Set Var

instance HasBV (HsBindLR GhcTc GhcTc) where
  getBV (FunBind{fun_id = L _ v}) = Set.singleton v
  getBV (AbsBinds {abs_exports = es}) = Set.fromList (map abe_poly es)
  getBV (PatBind {pat_lhs = pat}) = getBV pat
  getBV (VarBind {var_id = v}) = Set.singleton v
  getBV PatSynBind{} = Set.empty
  getBV XHsBindsLR{} = Set.empty

instance HasBV a => HasBV (GenLocated b a) where
  getBV (L _ e) = getBV e

instance HasBV a => HasBV [a] where
  getBV ps = foldl (\s p -> getBV p `Set.union` s) Set.empty ps



getConBV (PrefixCon ps) = getBV ps
getConBV (InfixCon p p') = getBV p `Set.union` getBV p'
getConBV (RecCon (HsRecFields {rec_flds = fs})) = foldl run Set.empty fs
      where run s (L _ f) = getBV (hsRecFieldArg f) `Set.union` s

instance HasBV (Pat GhcTc) where
  getBV (VarPat _ (L _ v)) = Set.singleton v
  getBV (LazyPat _ p) = getBV p
  getBV (AsPat _ (L _ v) p) = Set.insert v (getBV p)
  getBV (ParPat _ p) = getBV p
  getBV (BangPat _ p) = getBV p
  getBV (ListPat _ ps) = getBV ps
  getBV (TuplePat _ ps _) = getBV ps
  getBV (SumPat _ p _ _) = getBV p
  getBV (ConPatIn (L _ v) con) = Set.insert v (getConBV con)
  getBV (ConPatOut {pat_args = con}) = getConBV con
  getBV (ViewPat _ _ p) = getBV p
  getBV (SplicePat _ sp) =
    case sp of
      HsTypedSplice _ _ v _ -> Set.singleton v
      HsUntypedSplice _ _ v _ ->  Set.singleton v
      HsQuasiQuote _ p p' _ _ -> Set.fromList [p,p']
      HsSpliced _ _ (HsSplicedPat p) -> getBV p
      _ -> Set.empty
  getBV (NPlusKPat _ (L _ v) _ _ _ _) = Set.singleton v
  getBV (CoPat _ _ p _) = getBV p
  getBV (NPat {}) = Set.empty
  getBV (XPat p) = getBV p
  getBV (WildPat {}) = Set.empty
  getBV (LitPat {}) = Set.empty

#if __GLASGOW_HASKELL__ >= 808
  getBV (SigPat _ p _) =
#else
  getBV (SigPat _ p) =
#endif
    getBV p

#if __GLASGOW_HASKELL__ >= 810
instance HasBV NoExtCon where
#else
instance HasBV NoExt where
#endif
  getBV _ = Set.empty


-- | Syntax that may contain variables.
class HasFV a where
  -- | Compute the set of variables occurring in the given piece of
  -- syntax.  The name falsely suggests that returns free variables,
  -- but in fact it returns all variable occurrences, no matter
  -- whether they are free or bound.
  getFV :: a -> Set Var 

instance HasFV a => HasFV (GenLocated b a) where
  getFV (L _ e) = getFV e
  
instance HasFV a => HasFV [a] where
  getFV es = foldMap getFV es

instance HasFV a => HasFV (Bag a) where
  getFV es = foldMap getFV es

instance HasFV Var where
  getFV v = Set.singleton v

instance HasFV a => HasFV (MatchGroup GhcTc a) where
  getFV MG {mg_alts = alts} = getFV alts
  getFV XMatchGroup{} = Set.empty

instance HasFV a => HasFV (Match GhcTc a) where
  getFV Match {m_grhss = rhss} = getFV rhss
  getFV XMatch{} = Set.empty

instance HasFV (HsTupArg GhcTc) where
  getFV (Present _ e) = getFV e
  getFV _ = Set.empty


instance HasFV a => HasFV (GRHS GhcTc a) where
  getFV (GRHS _ g b) = getFV g `Set.union` getFV b
  getFV XGRHS{} = Set.empty

instance HasFV a => HasFV (GRHSs GhcTc a) where
  getFV GRHSs {grhssGRHSs = rhs, grhssLocalBinds = lbs} =
    getFV rhs `Set.union` getFV lbs
  getFV _ = Set.empty


instance HasFV (HsLocalBindsLR GhcTc GhcTc) where
  getFV (HsValBinds _ bs) = getFV bs
  getFV (HsIPBinds _ bs) = getFV bs
  getFV _ = Set.empty

instance HasFV (HsValBindsLR GhcTc GhcTc) where
  getFV (ValBinds _ b _) = getFV b
  getFV _ = Set.empty

instance HasFV (HsBindLR GhcTc GhcTc) where
  getFV FunBind {fun_matches = ms} = getFV ms
  getFV PatBind {pat_rhs = rhs} = getFV rhs
  getFV VarBind {var_rhs = rhs} = getFV rhs
  getFV AbsBinds {abs_binds = bs} = getFV bs
  getFV _ = Set.empty


instance HasFV (IPBind GhcTc) where
  getFV (IPBind _ _ e) = getFV e
  getFV _ = Set.empty

instance HasFV (HsIPBinds GhcTc) where
  getFV (IPBinds _ bs) = getFV bs
  getFV _ = Set.empty

instance HasFV (ApplicativeArg GhcTc) where
#if __GLASGOW_HASKELL__ >= 810
  getFV (ApplicativeArgOne _ _ e _ _)
#else
  getFV (ApplicativeArgOne _ _ e _)
#endif
    = getFV e
  getFV (ApplicativeArgMany _ es e _) = getFV es `Set.union` getFV e
  getFV XApplicativeArg{} = Set.empty

instance HasFV (ParStmtBlock GhcTc GhcTc) where
  getFV (ParStmtBlock _ es _ _) = getFV es
  getFV XParStmtBlock{} = Set.empty

instance HasFV a => HasFV (StmtLR GhcTc GhcTc a) where
  getFV (LastStmt _ e _ _) = getFV e
  getFV (BindStmt _ _ e _ _) = getFV e
  getFV (ApplicativeStmt _ args _) = foldMap (getFV . snd) args
  getFV (BodyStmt _ e _ _) = getFV e
  getFV (LetStmt _ bs) = getFV bs
  getFV (ParStmt _ stms e _) = getFV stms `Set.union` getFV e
  getFV TransStmt{} = Set.empty -- TODO
  getFV RecStmt{} = Set.empty -- TODO
  getFV XStmtLR{} = Set.empty

instance HasFV (HsRecordBinds GhcTc) where
  getFV HsRecFields{rec_flds = fs} = getFV fs

instance HasFV (HsRecField' o (LHsExpr GhcTc)) where
  getFV HsRecField {hsRecFieldArg = arg}  = getFV arg

instance HasFV (ArithSeqInfo GhcTc) where
  getFV (From e) = getFV e
  getFV (FromThen e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (FromTo e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (FromThenTo e1 e2 e3) = getFV e1 `Set.union` getFV e2 `Set.union` getFV e3

instance HasFV (HsBracket GhcTc) where
  getFV (ExpBr _ e) = getFV e
  getFV (VarBr _ _ e) = getFV e
  getFV _ = Set.empty

instance HasFV (HsCmd GhcTc) where
  getFV (HsCmdArrApp _ e1 e2 _ _) = getFV e1 `Set.union` getFV e2
  getFV (HsCmdArrForm _ e _ _ cmd) = getFV e `Set.union` getFV cmd
  getFV (HsCmdApp _ e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (HsCmdLam _ l) = getFV l
  getFV (HsCmdPar _ cmd) = getFV cmd
  getFV (HsCmdCase _ _ mg) = getFV mg
  getFV (HsCmdIf _ _ e1 e2 e3) = getFV e1 `Set.union` getFV e2 `Set.union` getFV e3
  getFV (HsCmdLet _ bs _) = getFV bs
  getFV (HsCmdDo _ cmd) = getFV cmd
  getFV (HsCmdWrap _ _ cmd) = getFV cmd
  getFV XCmd{} = Set.empty
  

instance HasFV (HsCmdTop GhcTc) where
  getFV (HsCmdTop _ cmd) = getFV cmd
  getFV XCmdTop{} = Set.empty

instance HasFV (HsExpr GhcTc) where
  getFV (HsVar _ v) = getFV v
  getFV HsUnboundVar {} = Set.empty
  getFV HsConLikeOut {} = Set.empty
  getFV HsRecFld {} = Set.empty
  getFV HsOverLabel {} = Set.empty
  getFV HsIPVar {} = Set.empty
  getFV HsOverLit {} = Set.empty
  getFV HsLit {} = Set.empty
  getFV (HsLam _ mg) = getFV mg
  getFV (HsLamCase _ mg) = getFV mg
  getFV (HsApp _ e1 e2) = getFV e1 `Set.union` getFV e2

#if __GLASGOW_HASKELL__ >= 808
  getFV (HsAppType _ e _)
#else
  getFV (HsAppType _ e)
#endif
    = getFV e
      
  getFV (OpApp _ e1 e2 e3) = getFV e1 `Set.union` getFV e2 `Set.union` getFV e3
  getFV (NegApp _ e _) = getFV e
  getFV (HsPar _ e) = getFV e
  getFV (SectionL _ e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (SectionR _ e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (ExplicitTuple _ es _) = getFV es
  getFV (ExplicitSum _ _ _ e) = getFV e
  getFV (HsCase _ e mg) = getFV e  `Set.union` getFV mg
  getFV (HsIf _ _ e1 e2 e3) = getFV e1 `Set.union` getFV e2 `Set.union` getFV e3
  getFV (HsMultiIf _ es) = getFV es
  getFV (HsLet _ bs e) = getFV bs `Set.union` getFV e
  getFV (HsDo _ _ e) = getFV e
  getFV (ExplicitList _ _ es) = getFV es
  getFV (RecordCon {rcon_flds = fs}) = getFV fs
  getFV (RecordUpd {rupd_expr = e, rupd_flds = fs}) = getFV e `Set.union` getFV fs

#if __GLASGOW_HASKELL__ >= 808
  getFV (ExprWithTySig _ e _)
#else
  getFV (ExprWithTySig _ e)
#endif
    = getFV e

  getFV (ArithSeq _ _ e) = getFV e
  getFV (HsSCC _ _ _ e) = getFV e
  getFV (HsCoreAnn _ _ _ e) = getFV e
  getFV (HsBracket _ e) = getFV e
  getFV HsRnBracketOut {} = Set.empty
  getFV HsTcBracketOut {} = Set.empty
  getFV HsSpliceE{} = Set.empty
  getFV (HsProc _ _ e) = getFV e
  getFV (HsStatic _ e) = getFV e

#if __GLASGOW_HASKELL__ < 810  
  getFV (HsArrApp _ e1 e2 _ _) = getFV e1 `Set.union` getFV e2
  getFV (HsArrForm _ e _ cmd) = getFV e `Set.union` getFV cmd
  getFV EWildPat {} = Set.empty
  getFV (EAsPat _ e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (EViewPat _ e1 e2) = getFV e1 `Set.union` getFV e2
  getFV (ELazyPat _ e) = getFV e
#endif
  
  getFV (HsTick _ _ e) = getFV e
  getFV (HsBinTick _ _ _ e) = getFV e
  getFV (HsTickPragma _ _ _ _ e) = getFV e
  getFV (HsWrap _ _ e) = getFV e
  getFV XExpr{} = Set.empty

