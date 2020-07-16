{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Rattus.Plugin.ScopeCheck (checkExpr, emptyCtx) where

import Rattus.Plugin.Utils 

import Prelude hiding ((<>))
import GhcPlugins
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

type LCtx = Set Var
data HiddenReason = BoxApp | AdvApp | NestedRec Var
type Hidden = Map Var HiddenReason

data Prim = Prim1 Prim1 | Prim2 Prim2
data Prim1 = Delay | Adv | Box | Unbox | Arr
data Prim2 = DApp | BApp | DAppP | BAppP

instance Outputable Prim1 where
  ppr Delay = "delay"
  ppr Adv = "adv"
  ppr Box = "box"
  ppr Unbox = "unbox"
  ppr Arr = "arr"
  
instance Outputable Prim2 where
  ppr DApp = "<*>"
  ppr BApp = "|*|"
  ppr DAppP = "<**"
  ppr BAppP = "|**"

instance Outputable Prim where
  ppr (Prim1 p) = ppr p
  ppr (Prim2 p) = ppr p

type RecDef = Set Var

data Ctx = Ctx
  { current :: LCtx,
    hidden :: Hidden,
    hiddenRec :: Hidden,
    earlier :: Maybe LCtx,
    srcLoc :: SrcSpan,
    recDef :: Maybe (RecDef,Var),
    stableTypes :: Set Var,
    primAlias :: Map Var Prim,
    stabilized :: Bool}

primMap :: Map FastString Prim
primMap = Map.fromList
  [("Delay", Prim1 Delay),
   ("delay", Prim1 Delay),
   ("adv", Prim1 Adv),
   ("box", Prim1 Box),
   ("arr", Prim1 Arr),
   ("unbox", Prim1 Unbox),
   ("<*>", Prim2 DApp),
   ("<**", Prim2 DAppP),
   ("|*|", Prim2 BApp),
   ("|**", Prim2 BAppP)
   ]


isPrim :: Ctx -> Var -> Maybe Prim
isPrim c v
  | Just p <- Map.lookup v (primAlias c) = Just p
  | otherwise = do
  (name,mod) <- getNameModule v
  if isRattModule mod then Map.lookup name primMap
  else Nothing



stabilize :: HiddenReason -> Ctx -> Ctx
stabilize hr c = c
  {current = Set.empty,
   earlier = Nothing,
   hidden = hidden c `Map.union` Map.fromSet (const hr) ctxHid,
   hiddenRec = hiddenRec c `Map.union` maybe Map.empty (Map.fromSet (const hr) . fst) (recDef c),
   recDef = Nothing,
   stabilized = True}
  where ctxHid = maybe (current c) (Set.union (current c)) (earlier c)


data Scope = Hidden SDoc | Visible | ImplUnboxed

getScope  :: Ctx -> Var -> Scope
getScope Ctx{recDef = Just (vs, recV), earlier = e} v
  | v `Set.member` vs =
    case e of
      Just _ -> Visible
      Nothing 
        | recV == v -> Hidden ("Recursive call to " <> ppr v <> " must occur under delay")
        | otherwise -> Hidden ("Mutually recursice call to " <> ppr v <> " must occur under delay")
  
--getScope Ctx{hiddenRecs = h} v
  -- recursive call that is out of scope
--  | (Set.member v h) = Hidden ""
getScope c v =
  case Map.lookup v (hiddenRec c) of
    Just (NestedRec rv) -> Hidden ("Recursive call to" <> ppr v <>
                            " is not allowed as it occurs in a local recursive definiton (namely of " <> ppr rv <> ")")
    Just BoxApp -> Hidden ("Recursive call to " <> ppr v <> " is not allowed since it occurs under a box")
    Just AdvApp -> Hidden ("This should not happen: recursive call to " <> ppr v <> " is out of scope due to adv")
    Nothing -> 
      case Map.lookup v (hidden c) of
        Just (NestedRec rv) ->
          if (isStable (stableTypes c) (varType v)) then Visible
          else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It appears in a local recursive definiton (namely of " <> ppr rv <> ")"
                       $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
        Just BoxApp ->
          if (isStable (stableTypes c) (varType v)) then Visible
          else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It occurs under " <> keyword "box" $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
        Just AdvApp -> Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs under adv.")
        Nothing
          | maybe False (Set.member v) (earlier c) ->
            if isStable (stableTypes c) (varType v) then Visible
            else Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                         "It occurs under delay" $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
          | Set.member v (current c) -> Visible
          | isTemporal (varType v) && isJust (earlier c) && userFunction v
            -> ImplUnboxed
          | otherwise -> Visible



pickFirst :: SrcSpan -> SrcSpan -> SrcSpan
pickFirst s@RealSrcSpan{} _ = s
pickFirst _ s = s

printMessage' :: Severity -> Ctx -> Var -> SDoc -> CoreM ()
printMessage' sev cxt var doc =
  printMessage sev (pickFirst (srcLoc cxt) (nameSrcSpan (varName var))) doc

printMessageCheck :: Severity -> Ctx -> Var -> SDoc -> CoreM Bool
printMessageCheck sev cxt var doc = printMessage' sev cxt var doc >>
  case sev of
    SevError -> return False
    _ -> return True



emptyCtx :: Maybe (Set Var,Var) -> Ctx
emptyCtx mvar =
  Ctx { current =  Set.empty,
        earlier = Nothing,
        hidden = Map.empty,
        hiddenRec = Map.empty,
        srcLoc = UnhelpfulSpan "<no location info>",
        recDef = mvar,
        primAlias = Map.empty,
        stableTypes = Set.empty,
        stabilized = isJust mvar}


isPrimExpr :: Ctx -> Expr Var -> Maybe (Prim,Var)
isPrimExpr c (App e (Type _)) = isPrimExpr c e
isPrimExpr c (App e e') | not $ tcIsLiftedTypeKind $ typeKind $ exprType e' = isPrimExpr c e
isPrimExpr c (Var v) = fmap (,v) (isPrim c v)
isPrimExpr c (Tick _ e) = isPrimExpr c e
isPrimExpr c (Lam v e)
  | isTyVar v || (not $ tcIsLiftedTypeKind $ typeKind $ varType v) = isPrimExpr c e
isPrimExpr _ _ = Nothing


isStableConstr :: Type -> CoreM (Maybe Var)
isStableConstr t = 
  case splitTyConApp_maybe t of
    Just (con,[args]) ->
      case getNameModule con of
        Just (name, mod) ->
          if isRattModule mod && name == "Stable"
          then return (getTyVar_maybe args)
          else return Nothing
        _ -> return Nothing                           
    _ ->  return Nothing

checkExpr :: Ctx -> Expr Var -> CoreM Bool
checkExpr c (App e e') | isType e' || (not $ tcIsLiftedTypeKind $ typeKind $ exprType e')
  = checkExpr c e
checkExpr c@Ctx{current = cur, hidden = hid, earlier = earl} (App e1 e2) =
  case isPrimExpr c e1 of
    Just (Prim1 p,v) -> case p of
      Box -> do
        ch <- checkExpr (stabilize BoxApp c) e2
        -- don't bother with a warning if the scopecheck fails
        when (ch && stabilized c)  (printMessage' SevWarning c v
          (text "box nested inside another box or recursive definition can cause time leaks"))
        return ch
      Arr -> do
        ch <- checkExpr (stabilize BoxApp c) e2
        -- don't bother with a warning if the scopecheck fails
        when (ch && stabilized c)  (printMessage' SevWarning c v
          (text "arr nested inside a box or recursive definition can cause time leaks"))
        return ch

      Unbox -> checkExpr c e2
      Delay -> case earl of
        Just _ -> printMessageCheck SevError c v (text "cannot delay more than once")
        Nothing -> checkExpr c{current = Set.empty, earlier = Just cur} e2
      Adv -> case earl of
        Just er -> checkExpr c{earlier = Nothing, current = er,
                               hidden = hid `Map.union` Map.fromSet (const AdvApp) cur} e2
        Nothing -> printMessageCheck SevError c v (text "can only advance under delay")
    _ -> liftM2 (&&) (checkExpr c e1)  (checkExpr c e2)
checkExpr c (Case e v _ alts) =
    liftM2 (&&) (checkExpr c e) (liftM and (mapM (\ (_,vs,e)-> checkExpr (addVars vs c') e) alts))
  where c' = addVars [v] c
checkExpr c@Ctx{earlier = Just _} (Lam v _) =
  printMessageCheck SevError c v (text "Functions may not be defined under delay."
                                  $$ "In order to define a function under delay, you have to wrap it in box.")
checkExpr c (Lam v e)
  | isTyVar v || (not $ tcIsLiftedTypeKind $ typeKind $ varType v) = do
      is <- isStableConstr (varType v)
      let c' = case is of
            Nothing -> c
            Just t -> c{stableTypes = Set.insert t (stableTypes c)}
      checkExpr c' e
  | otherwise = checkExpr (addVars [v] c) e
checkExpr _ (Type _)  = return True
checkExpr _ (Lit _)  = return True
checkExpr _ (Coercion _)  = return True
checkExpr c (Tick (SourceNote span _name) e) =
  checkExpr c{srcLoc = RealSrcSpan span} e
checkExpr c (Tick _ e) = checkExpr c e
checkExpr c (Cast e _) = checkExpr c e
checkExpr c (Let (NonRec v e1) e2) =
  case isPrimExpr c e1 of
    Just (p,_) -> (checkExpr (c{primAlias = Map.insert v p (primAlias c)}) e2)
    Nothing -> liftM2 (&&) (checkExpr c e1)  (checkExpr (addVars [v] c) e2)
checkExpr _ (Let (Rec ([])) _) = return True
checkExpr c (Let (Rec binds) e2) = do
    r1 <- mapM (\ (v,e) -> checkExpr (c' v) e) binds
    r2 <- checkExpr (addVars vs c) e2
    let r = (and r1 && r2)  
    when (r && stabilized c) (printMessage' SevWarning c (head vs)
          (text "recursive definition nested inside a box or annother recursive definition can cause time leaks"))
    return r
  where vs = map fst binds
        vs' = Set.fromList vs
        ctxHid = maybe (current c) (Set.union (current c)) (earlier c)
        recHid = maybe ctxHid (Set.union ctxHid . fst) (recDef c)
        c' v = c {current = Set.empty,
                  earlier = Nothing,
                  hidden =  hidden c `Map.union`
                   (Map.fromSet (const (NestedRec v)) recHid),
                  recDef = Just (vs',v),
                  stabilized = True}
checkExpr c@Ctx{earlier = earl}  (Var v)
  | tcIsLiftedTypeKind $ typeKind $ varType v =
    case isPrim c v of
      Just (Prim1 _) ->
        printMessageCheck SevError c v (ppr v <> text " must be applied to an argument")
      Just (Prim2 p) ->
        let dapp = case earl of
              Just _ ->
                printMessageCheck SevError c v (ppr v <> text " may not be used under delay")
              _ -> return True
 
        in case p of
             DApp -> dapp
             DAppP -> dapp
             BApp -> return True
             BAppP -> return True
      _ -> case getScope c v of
             Hidden reason -> printMessageCheck SevError c v reason
             Visible -> return True
             ImplUnboxed -> printMessageCheck SevWarning c v
                (ppr v <> text " is an external temporal function used under delay, which may cause time leaks")

  | otherwise = return True





addVars :: [Var] -> Ctx -> Ctx
addVars v c = c{current = Set.fromList v `Set.union` current c }

