{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}



-- | This module implements the source plugin that checks the variable
-- scope of of Rattus programs.

module Rattus.Plugin.ScopeCheck (checkAll) where

import Rattus.Plugin.Utils
import Rattus.Plugin.Dependency
import Rattus.Plugin.Annotation

import Prelude hiding ((<>))
import GhcPlugins
import TcRnTypes
import Bag

#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Extension
import GHC.Hs.Expr
import GHC.Hs.Pat
import GHC.Hs.Binds
#else 
import HsExtension
import HsExpr
import HsPat
import HsBinds
#endif

import Data.Graph
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)
import System.Exit
import Data.Maybe

import Control.Monad

-- | The current context for scope checking
data Ctxt = Ctxt
  {
    -- | Variables that are in scope now (i.e. occurring in the typing
    -- context but not to the left of a tick)
    current :: LCtxt,
    -- | Variables that are in the typing context, but to the left of a
    -- tick
    earlier :: Maybe LCtxt,
    -- | Variables that have fallen out of scope. The map contains the
    -- reason why they have fallen out of scope.
    hidden :: Hidden,
    -- | Same as 'hidden' but for recursive variables.
    hiddenRec :: Hidden,
    -- | The current location information.
    srcLoc :: SrcSpan,
    -- | If we are in the body of a recursively defined function, this
    -- field contains the variables that are defined recursively
    -- (could be more than one due to mutual recursion or because of a
    -- recursive pattern definition) and the location of the recursive
    -- definition.
    recDef :: Maybe RecDef,
    -- | Type variables with a 'Stable' constraint attached to them.
    stableTypes :: Set Var,
    -- | A mapping from variables to the primitives that they are
    -- defined equal to. For example, a program could contain @let
    -- mydel = delay in mydel 1@, in which case @mydel@ is mapped to
    -- 'Delay'.
    primAlias :: Map Var Prim,
    -- | This flag indicates whether the context was 'stabilized'
    -- (stripped of all non-stable stuff). It is set when typechecking
    -- 'box', 'arr' and guarded recursion.
    stabilized :: Bool}
  deriving Show


-- | The starting context for checking a top-level definition. For
-- non-recursive definitions, the argument is @Nothing@. Otherwise, it
-- contains the recursively defined variables along with the location
-- of the recursive definition.
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

-- | A local context, consisting of a set of variables.
type LCtxt = Set Var

-- | The recursively defined variables + the position where the
-- recursive definition starts
type RecDef = (Set Var, SrcSpan)

-- | Indicates, why a variable has fallen out of scope.
data HiddenReason = NestedRec SrcSpan | FunDef | BoxApp | AdvApp | ArrowNotation deriving Show

-- | Hidden context, containing variables that have fallen out of
-- context along with the reason why they have.
type Hidden = Map Var HiddenReason

-- | The 4 primitive Rattus operations plus 'arr'.
data Prim = Delay | Adv | Box | Unbox | Arr deriving Show

-- | This constraint is used to pass along the context implicitly via
-- an implicit parameter.
type GetCtxt = ?ctxt :: Ctxt


-- | This type class is implemented for each AST type @a@ for which we
-- can check whether it adheres to the scoping rules of Rattus.
class Scope a where
  -- | Check whether the argument is a scope correct piece of syntax
  -- in the given context.
  check :: GetCtxt => a -> TcM Bool

-- | This is a variant of 'Scope' for syntax that can also bind
-- variables.
class ScopeBind a where
  -- | 'checkBind' checks whether its argument is scope-correct and in
-- addition returns the the set of variables bound by it.
  checkBind :: GetCtxt => a -> TcM (Bool,Set Var)


-- | set the current context.
setCtxt :: Ctxt -> (GetCtxt => a) -> a 
setCtxt c a = let ?ctxt = c in a


-- | modify the current context.
modifyCtxt :: (Ctxt -> Ctxt) -> (GetCtxt => a) -> (GetCtxt => a)
modifyCtxt f a =
  let newc = f ?ctxt in
  let ?ctxt = newc in a


-- | Check all definitions in the given module. If Scope errors are
-- found, the current execution is halted with 'exitFailure'.
checkAll :: TcGblEnv -> TcM ()
checkAll env = do
  let bindDep = filter (filterBinds (tcg_mod env) (tcg_ann_env env)) (dependency (tcg_binds env))
  res <- mapM checkSCC bindDep
  if and res then return () else liftIO exitFailure

-- | This function checks whether a given top-level definition (either
-- a single non-recursive definition or a group of mutual recursive
-- definitions) is marked as Rattus code (via an annotation). In a
-- group of mutual recursive definitions, the whole group is
-- considered Rattus code if at least one of its constituents is
-- marked as such.
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


instance Scope a => Scope (Match GhcTc a) where
  check Match{m_pats=ps,m_grhss=rhs} = mod `modifyCtxt` check rhs
    where mod c = addVars (getBV ps) (if null ps then c else stabilizeLater c)
  check XMatch{} = return True

instance Scope a => Scope (MatchGroup GhcTc a) where
  check MG {mg_alts = alts} = check alts
  check XMatchGroup {} = return True

instance Scope a => ScopeBind (StmtLR GhcTc GhcTc a) where
  checkBind (LastStmt _ b _ _) =  ( , Set.empty) <$> check b
  checkBind (BindStmt _ p b _ _) = do
    let vs = getBV p
    let c' = addVars vs ?ctxt
    r <- setCtxt c' (check b)
    return (r,vs)
  checkBind (BodyStmt _ b _ _) = ( , Set.empty) <$> check b
  checkBind (LetStmt _ bs) = checkBind bs
  checkBind ParStmt{} = notSupported "monad comprehensions"
  checkBind TransStmt{} = notSupported "monad comprehensions"
  checkBind ApplicativeStmt{} = notSupported "applicative do notation"
  checkBind RecStmt{} = notSupported "recursive do notation"
  checkBind XStmtLR {} = return (True,Set.empty)


instance ScopeBind a => ScopeBind [a] where
  checkBind [] = return (True,Set.empty)
  checkBind (x:xs) = do
    (r,vs) <- checkBind x
    (r',vs') <- addVars vs `modifyCtxt` (checkBind xs)
    return (r && r',vs `Set.union` vs')

instance ScopeBind a => ScopeBind (GenLocated SrcSpan a) where
  checkBind (L l x) =  (\c -> c {srcLoc = l}) `modifyCtxt` checkBind x


instance Scope a => Scope (GRHS GhcTc a) where
  check (GRHS _ gs b) = do
    (r, vs) <- checkBind gs
    r' <- addVars vs `modifyCtxt`  (check b)
    return (r && r')
  check XGRHS{} = return True

instance ScopeBind (SCC (LHsBindLR GhcTc GhcTc, Set Var)) where
  checkBind (AcyclicSCC (b,vs)) = (, vs) <$> check b
  checkBind (CyclicSCC bs) = do
    res <- fmap and (mapM check' bs')
    when (res && stabilized ?ctxt) 
      (printMessage' SevWarning
        (text "recursive definition nested inside a box or annother recursive definition can cause time leaks"))
    return (res, vs)
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
  
  checkBind (XValBindsLR (NValBinds binds _)) = checkBind binds


instance ScopeBind (HsBindLR GhcTc GhcTc) where
  checkBind b = (, getBV b) <$> check b


-- | Compute the set of variables defined by the given Haskell binder.
getAllBV :: GenLocated l (HsBindLR GhcTc GhcTc) -> Set Var
getAllBV (L _ b) = getAllBV' b where
  getAllBV' (FunBind{fun_id = L _ v}) = Set.singleton v
  getAllBV' (AbsBinds {abs_exports = es, abs_binds = bs}) = Set.fromList (map abe_poly es) `Set.union` foldMap getBV bs
  getAllBV' (PatBind {pat_lhs = pat}) = getBV pat
  getAllBV' (VarBind {var_id = v}) = Set.singleton v
  getAllBV' PatSynBind{} = Set.empty
  getAllBV' XHsBindsLR{} = Set.empty


instance ScopeBind (RecFlag, LHsBinds GhcTc) where
  checkBind (NonRecursive, bs)  = checkBind $ bagToList bs
  checkBind (Recursive, bs)  = do
    res <- fmap and (mapM check' bs')
    when (res && stabilized ?ctxt) 
      (printMessage' SevWarning
        (text "recursive definition nested inside a box or annother recursive definition can cause time leaks"))
    return (res, vs)
    where bs' = bagToList bs
          vs = foldMap getAllBV bs'
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


instance ScopeBind (HsLocalBindsLR GhcTc GhcTc) where
  checkBind (HsValBinds _ bs) = checkBind bs
  checkBind HsIPBinds {} = notSupported "implicit parameters"
  checkBind EmptyLocalBinds{} = return (True,Set.empty)
  checkBind XHsLocalBindsLR{} = return (True,Set.empty)

instance Scope a => Scope (GRHSs GhcTc a) where
  check GRHSs{grhssGRHSs = rhs, grhssLocalBinds = lbinds} = do
    (l,vs) <- checkBind lbinds
    r <- addVars vs `modifyCtxt` (check rhs)
    return (r && l)
  check XGRHSs{} = return True

instance Show Var where
  show v = getOccString v

instance Scope (HsExpr GhcTc) where
  check (HsVar _ (L _ v))
    | Just p <- isPrim v =
        case p of
          Unbox -> return True
          _ -> printMessageCheck SevError ("Defining an alias for " <> ppr v <> " is not allowed")
    | otherwise = case getScope v of
             Hidden reason -> printMessageCheck SevError reason
             Visible -> return True
             ImplUnboxed -> printMessageCheck SevWarning 
                (ppr v <> text " is an external temporal function used under delay, which may cause time leaks")
  check (HsApp _ e1 e2) =
    case isPrimExpr e1 of
    Just (p,_) -> case p of
      Box -> do
        ch <- stabilize BoxApp `modifyCtxt` check e2
        -- don't bother with a warning if the scopecheck fails
        when (ch && stabilized ?ctxt) --TODO  && not (isStable (stableTypes ?ctxt) (exprType e2)))
          (printMessage' SevWarning
           (text "When box is used inside another box or a recursive definition, it can cause time leaks"))
        return ch
      Arr -> do
        ch <- stabilize BoxApp `modifyCtxt` check e2
        -- don't bother with a warning if the scopecheck fails
        when (ch && stabilized ?ctxt) -- && not (isStable (stableTypes c) (exprType e2)))
          (printMessage' SevWarning
            (text "When arr is used inside box or a recursive definition, it can cause time leaks"))
        return ch

      Unbox -> check e2
      Delay -> case earlier ?ctxt of
        Just _ -> printMessageCheck SevError (text "cannot delay more than once")
        Nothing -> (\c -> c{current = Set.empty, earlier = Just (current ?ctxt)})
                  `modifyCtxt` check  e2
      Adv -> case earlier ?ctxt of
        Just er -> mod `modifyCtxt` check e2
          where mod c =  c{earlier = Nothing, current = er,
                           hidden = hidden ?ctxt `Map.union`
                            Map.fromSet (const AdvApp) (current ?ctxt)}
        Nothing -> printMessageCheck SevError (text "can only advance under delay")
    _ -> liftM2 (&&) (check e1)  (check e2)
  check HsUnboundVar{}  = return True
  check HsConLikeOut{} = return True
  check HsRecFld{} = return True
  check HsOverLabel{} = return True
  check HsIPVar{} = notSupported "implicit parameters"
  check HsOverLit{} = return True
  
#if __GLASGOW_HASKELL__ >= 808
  check (HsAppType _ e _)
#else
  check (HsAppType _ e)
#endif
    = check e
  
  check (HsTick _ _ e) = check e
  check (HsBinTick _ _ _ e) = check e  
  check (HsSCC _ _ _ e) = check e
  check (HsPar _ e) = check e
  check (HsWrap _ _ e) = check e
  check HsLit{} = return True
  check (OpApp _ e1 e2 e3) = and <$> mapM check [e1,e2,e3]
  check (HsLam _ mg) = stabilizeLater `modifyCtxt` check mg
  check (HsLamCase _ mg) = stabilizeLater `modifyCtxt` check mg
  check (HsIf _ _ e1 e2 e3) = and <$> mapM check [e1,e2,e3]
  check (HsCase _ e1 e2) = (&&) <$> check e1 <*> check e2
  check (SectionL _ e1 e2) = (&&) <$> check e1 <*> check e2
  check (SectionR _ e1 e2) = (&&) <$> check e1 <*> check e2
  check (ExplicitTuple _ e _) = check e
  check (HsLet _ bs e) = do
    (l,vs) <- checkBind bs
    r <- addVars vs `modifyCtxt` (check e)
    return (r && l)
  check (NegApp _ e _) = check e
  check (ExplicitSum _ _ _ e) = check e
  check (HsMultiIf _ e) = check e
  check (ExplicitList _ _ e) = check e
  check RecordCon { rcon_flds = f} = check f
  check RecordUpd { rupd_expr = e, rupd_flds = fs} = (&&) <$> check e <*> check fs
#if __GLASGOW_HASKELL__ >= 808
  check (ExprWithTySig _ e _)
#else
  check (ExprWithTySig _ e)
#endif
    = check e
  check (ArithSeq _ _ e) = check e
  check HsBracket{} = notSupported "MetaHaskell"
  check HsRnBracketOut{} = notSupported "MetaHaskell"
  check HsTcBracketOut{} = notSupported "MetaHaskell"
  check HsSpliceE{} = notSupported "Template Haskell"
  check (HsProc _ p e) = mod `modifyCtxt` check e
    where mod c = addVars (getBV p) (stabilize ArrowNotation c)
  check (HsStatic _ e) = check e
  check (HsDo _ _ e) = fst <$> checkBind e
  check (HsCoreAnn _ _ _ e) = check e
  check (HsTickPragma _ _ _ _ e) = check e
  check XExpr {} = return True
#if __GLASGOW_HASKELL__ < 810
  check HsArrApp{} = impossible
  check HsArrForm{} = impossible
  check EWildPat{} = impossible
  check EAsPat{} = impossible
  check EViewPat{} = impossible
  check ELazyPat{} = impossible

impossible :: GetCtxt => TcM Bool
impossible = printMessageCheck SevError "This syntax should never occur after typechecking"
#endif


instance Scope (HsCmdTop GhcTc) where
  check (HsCmdTop _ e) = check e
  check XCmdTop{} = return True

instance Scope (HsCmd GhcTc) where
  check (HsCmdArrApp _ e1 e2 _ _) = (&&) <$> check e1 <*> check e2
  check (HsCmdDo _ e) = fst <$> checkBind e
  check (HsCmdArrForm _ e1 _ _ e2) = (&&) <$> check e1 <*> check e2
  check (HsCmdApp _ e1 e2) = (&&) <$> check e1 <*> check e2
  check (HsCmdLam _ e) = check e
  check (HsCmdPar _ e) = check e
  check (HsCmdCase _ e1 e2) = (&&) <$> check e1 <*> check e2
  check (HsCmdIf _ _ e1 e2 e3) = (&&) <$> ((&&) <$> check e1 <*> check e2) <*> check e3
  check (HsCmdLet _ bs e) = do
    (l,vs) <- checkBind bs
    r <- addVars vs `modifyCtxt` (check e)
    return (r && l)
  check (HsCmdWrap _ _ e) = check e
  check XCmd{} = return True


-- | This is used when checking function definitions. If the context
-- is not ticked, it stays the same. Otherwise, it is stabilized
-- (similar to 'box').
stabilizeLater :: Ctxt -> Ctxt
stabilizeLater c =
  if isJust (earlier c)
  then c {earlier = Nothing,
          hidden = hid,
          hiddenRec = maybe (hiddenRec c) (Map.union (hidden c) . Map.fromSet (const FunDef))
                      (fst <$> recDef c),
          recDef = Nothing}
  else c
  where hid = maybe (hidden c) (Map.union (hidden c) . Map.fromSet (const FunDef)) (earlier c)


instance Scope (ArithSeqInfo GhcTc) where
  check (From e) = check e
  check (FromThen e1 e2) = (&&) <$> check e1 <*> check e2
  check (FromTo e1 e2) = (&&) <$> check e1 <*> check e2
  check (FromThenTo e1 e2 e3) = (&&) <$> ((&&) <$> check e1 <*> check e2) <*> check e3

instance Scope (HsRecordBinds GhcTc) where
  check HsRecFields {rec_flds = fs} = check fs

instance Scope (HsRecField' a (LHsExpr GhcTc)) where
  check HsRecField{hsRecFieldArg = a} = check a

instance Scope (HsTupArg GhcTc) where
  check (Present _ e) = check e
  check Missing{} = return True
  check XTupArg{} = return True
  
instance Scope (HsBindLR GhcTc GhcTc) where
  check AbsBinds {abs_binds = binds, abs_ev_vars  = ev} = mod `modifyCtxt` check binds
    where mod c = c { stableTypes= stableTypes c `Set.union`
                      Set.fromList (mapMaybe (isStableConstr . varType) ev)}
  check FunBind{fun_matches= matches, fun_id = L _ v} = mod `modifyCtxt` check matches
    where mod c = c { stableTypes= stableTypes c `Set.union`
                      Set.fromList (extractStableConstr (varType v))}
  check PatBind{pat_lhs = lhs, pat_rhs=rhs} = addVars (getBV lhs) `modifyCtxt` check rhs
  check VarBind{var_rhs = rhs} = check rhs
  check PatSynBind {} = return True -- pattern synonyms are not supported
  check XHsBindsLR {} = return True


-- | Checks whether the given type is a type constraint of the form
-- @Stable a@ for some type variable @a@. In that case it returns the
-- type variable @a@.
isStableConstr :: Type -> Maybe TyVar
isStableConstr t = 
  case splitTyConApp_maybe t of
    Just (con,[args]) ->
      case getNameModule con of
        Just (name, mod) ->
          if isRattModule mod && name == "Stable"
          then (getTyVar_maybe args)
          else Nothing
        _ -> Nothing                           
    _ ->  Nothing


-- | Given a type @(C1, ... Cn) => t@, this function returns the list
-- of type variables @[a1,...,am]@ for which there is a constraint
-- @Stable ai@ among @C1, ... Cn@.
extractStableConstr :: Type -> [TyVar]
extractStableConstr  = mapMaybe isStableConstr . fst . splitFunTys . snd . splitForAllTys


-- | Checks a top-level definition group, which is either a single
-- non-recursive definition or a group of (mutual) recursive
-- definitions.

checkSCC :: SCC (LHsBindLR  GhcTc GhcTc, Set Var) -> TcM Bool
checkSCC (AcyclicSCC (b,_)) = setCtxt (emptyCtxt Nothing) (check b)

checkSCC (CyclicSCC bs) = (fmap and (mapM check' bs'))
  where bs' = map fst bs
        vs = foldMap snd bs
        check' b@(L l _) = setCtxt (emptyCtxt (Just (vs,l))) (check b)

-- | Stabilizes the given context, i.e. remove all non-stable types
-- and any tick. This is performed on checking 'box', 'arr' and
-- guarded recursive definitions. To provide better error messages a
-- reason has to be given as well.
stabilize :: HiddenReason -> Ctxt -> Ctxt
stabilize hr c = c
  {current = Set.empty,
   earlier = Nothing,
   hidden = hidden c `Map.union` Map.fromSet (const hr) ctxHid,
   hiddenRec = hiddenRec c `Map.union` maybe Map.empty (Map.fromSet (const hr) . fst) (recDef c),
   recDef = Nothing,
   stabilized = True}
  where ctxHid = maybe (current c) (Set.union (current c)) (earlier c)

data VarScope = Hidden SDoc | Visible | ImplUnboxed


-- | This function checks whether the given variable is in scope.
getScope  :: GetCtxt => Var -> VarScope
getScope v =
  case ?ctxt of
    Ctxt{recDef = Just (vs,_), earlier = e}
      | v `Set.member` vs ->
        case e of
          Just _ -> Visible
          Nothing -> Hidden ("(Mutually) recursive call to " <> ppr v <> " must occur under delay")
    _ ->
      case Map.lookup v (hiddenRec ?ctxt) of
        Just (NestedRec rv) -> Hidden ("Recursive call to" <> ppr v <>
                            " is not allowed as it occurs in a local recursive definiton (at " <> ppr rv <> ")")
        Just BoxApp -> Hidden ("Recursive call to " <> ppr v <> " is not allowed here, since it occurs under a box")
        Just ArrowNotation -> Hidden ("Recursive call to " <> ppr v <> " is not allowed here, since it occurs inside an arrow notation")
        Just FunDef -> Hidden ("Recursive call to " <> ppr v <> " is not allowed here, since it occurs in a function that is defined under delay")
        Just AdvApp -> Hidden ("This should not happen: recursive call to " <> ppr v <> " is out of scope due to adv")
        Nothing -> 
          case Map.lookup v (hidden ?ctxt) of
            Just (NestedRec rv) ->
              if (isStable (stableTypes ?ctxt) (varType v)) then Visible
              else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It appears in a local recursive definiton (at " <> ppr rv <> ")"
                       $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
            Just BoxApp ->
              if (isStable (stableTypes ?ctxt) (varType v)) then Visible
              else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It occurs under " <> keyword "box" $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
            Just ArrowNotation ->
              if (isStable (stableTypes ?ctxt) (varType v)) then Visible
              else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It occurs under inside an arrow notation and is of type " <> ppr (varType v) <> ", which is not stable.")
            Just AdvApp -> Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs under adv.")
            Just FunDef -> if (isStable (stableTypes ?ctxt) (varType v)) then Visible
              else Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs in a function that is defined under a delay, is a of a non-stable type " <> ppr (varType v) <> ", and is bound outside delay")
            Nothing
              | maybe False (Set.member v) (earlier ?ctxt) ->
                if isStable (stableTypes ?ctxt) (varType v) then Visible
                else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                         "It occurs under delay" $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
              | Set.member v (current ?ctxt) -> Visible
              | isTemporal (varType v) && isJust (earlier ?ctxt) && userFunction v
                -> ImplUnboxed
              | otherwise -> Visible

-- | A map from the syntax of a primitive of Rattus to 'Prim'.
primMap :: Map FastString Prim
primMap = Map.fromList
  [("Delay", Delay),
   ("delay", Delay),
   ("adv", Adv),
   ("box", Box),
   ("arr", Arr),
   ("unbox", Unbox)]


-- | Checks whether a given variable is in fact a Rattus primitive.
isPrim :: GetCtxt => Var -> Maybe Prim
isPrim v
  | Just p <- Map.lookup v (primAlias ?ctxt) = Just p
  | otherwise = do
  (name,mod) <- getNameModule v
  if isRattModule mod then Map.lookup name primMap
  else Nothing


-- | Checks whether a given expression is in fact a Rattus primitive.
isPrimExpr :: GetCtxt => LHsExpr GhcTc -> Maybe (Prim,Var)
isPrimExpr (L _ e) = isPrimExpr' e where
  isPrimExpr' :: GetCtxt => HsExpr GhcTc -> Maybe (Prim,Var)
  isPrimExpr' (HsVar _ (L _ v)) = fmap (,v) (isPrim v)
  
#if __GLASGOW_HASKELL__ >= 808
  isPrimExpr' (HsAppType _ e _)
#else
  isPrimExpr' (HsAppType _ e)
#endif
    = isPrimExpr e
  isPrimExpr' (HsTick _ _ e) = isPrimExpr e
  isPrimExpr' (HsBinTick _ _ _ e) = isPrimExpr e  
  isPrimExpr' (HsSCC _ _ _ e) = isPrimExpr e
  isPrimExpr' (HsWrap _ _ e) = isPrimExpr' e
  isPrimExpr' (HsPar _ e) = isPrimExpr e
  isPrimExpr' _ = Nothing


-- | This type class provides default implementations for 'check' and
-- 'checkBind' for Haskell syntax that is not supported. These default
-- implementations simply print an error message.
class NotSupported a where
  notSupported :: GetCtxt => SDoc -> TcM a

instance NotSupported Bool where
  notSupported doc = printMessageCheck SevError ("Rattus does not support " <> doc)

instance NotSupported (Bool,Set Var) where
  notSupported doc = (,Set.empty) <$> notSupported doc


-- | Add variables to the current context.
addVars :: Set Var -> Ctxt -> Ctxt
addVars vs c = c{current = vs `Set.union` current c }

-- | Print a message with the current location.
printMessage' :: GetCtxt => Severity -> SDoc ->  TcM ()
printMessage' sev doc = printMessage sev (srcLoc ?ctxt) doc

-- | Print a message with the current location. Returns 'False', if
-- the severity is 'SevError' and otherwise 'True.
printMessageCheck :: GetCtxt =>  Severity -> SDoc -> TcM Bool
printMessageCheck sev doc = printMessage' sev doc >>
  case sev of
    SevError -> return False
    _ -> return True
