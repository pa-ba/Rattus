{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | This module implements the check that the transformed code is
-- typable in the single tick calculus.

module Rattus.Plugin.CheckSingleTick
  (checkExpr, emptyCtx) where


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
data HiddenReason = BoxApp | AdvApp | NestedRec Var | FunDef | DelayApp
type Hidden = Map Var HiddenReason

data Prim = Delay | Adv | Box | Arr


instance Outputable Prim where
  ppr Delay = "delay"
  ppr Adv = "adv"
  ppr Box = "box"
  ppr Arr = "arr"
  
data Ctx = Ctx
  { current :: LCtx,
    hidden :: Hidden,
    earlier :: Maybe LCtx,
    srcLoc :: SrcSpan,
    recDef :: Set Var, -- ^ recursively defined variables 
    stableTypes :: Set Var,
    primAlias :: Map Var Prim,
    -- number of ticks (for recursive calls). This is to allow
    -- recursive definitions of the form @f = delay (delay (adv f))@.
    ticks :: Int} 

primMap :: Map FastString Prim
primMap = Map.fromList
  [--("Delay", Delay),
   ("delay", Delay),
   ("adv", Adv),
   ("box", Box),
   ("arr", Arr)
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
   ticks = 0}
  where ctxHid = maybe (current c) (Set.union (current c)) (earlier c)


data Scope = Hidden SDoc | Visible | ImplUnboxed

getScope  :: Ctx -> Var -> Scope
getScope c v =
    if v `Set.member` recDef c then
      if ticks c > 0 then Visible
      else Hidden ("(Mutually) recursive call to " <> ppr v <> " must occur under delay")
    else case Map.lookup v (hidden c) of
      Just reason ->
        if (isStable (stableTypes c) (varType v)) then Visible
        else case reason of
          NestedRec rv -> Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$ "It appears in a local recursive definition (namely of " <> ppr rv <> ")"
                       $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
          BoxApp -> Hidden ("Variable " <> ppr v <> " is no longer in scope:" $$
                       "It occurs under " <> keyword "box" $$ "and is of type " <> ppr (varType v) <> ", which is not stable.")
          AdvApp -> Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs under adv.")
        
          FunDef -> Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs in a function that is defined under a delay, is a of a non-stable type " <> ppr (varType v) <> ", and is bound outside delay")
          DelayApp -> Hidden ("Variable " <> ppr v <> " is no longer in scope: It occurs under two occurrences of delay and is a of a non-stable type " <> ppr (varType v))
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



emptyCtx :: Set Var -> Ctx
emptyCtx vars =
  Ctx { current =  Set.empty,
        earlier = Nothing,
        hidden = Map.empty,
        srcLoc = UnhelpfulSpan "<no location info>",
        recDef = vars,
        primAlias = Map.empty,
        stableTypes = Set.empty,
        ticks = 0}


isPrimExpr :: Ctx -> Expr Var -> Maybe (Prim,Var)
isPrimExpr c (App e (Type _)) = isPrimExpr c e
isPrimExpr c (App e e') | not $ tcIsLiftedTypeKind $ typeKind $ exprType e' = isPrimExpr c e
isPrimExpr c (Var v) = fmap (,v) (isPrim c v)
isPrimExpr c (Tick _ e) = isPrimExpr c e
isPrimExpr c (Lam v e)
  | isTyVar v || (not $ tcIsLiftedTypeKind $ typeKind $ varType v) = isPrimExpr c e
isPrimExpr _ _ = Nothing


stabilizeLater :: Ctx -> Ctx
stabilizeLater c =
  case earlier c of
    Just earl -> c {earlier = Nothing,
                    hidden = hidden c `Map.union` Map.fromSet (const FunDef) earl}
    Nothing -> c 

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
    Just (p,v) -> case p of
      Box -> do
        checkExpr (stabilize BoxApp c) e2
      Arr -> do
        checkExpr (stabilize BoxApp c) e2

      Delay -> case earl of
        Just earl' ->
          checkExpr c{current = Set.empty, earlier = Just cur,
                      ticks = ticks c + 1, hidden = hidden c `Map.union` Map.fromSet (const DelayApp) earl'} e2
        Nothing -> checkExpr c{current = Set.empty, earlier = Just cur, ticks = ticks c + 1} e2
      Adv -> case earl of
        Just er -> checkExpr c{earlier = Nothing, current = er, ticks = ticks c - 1,
                               hidden = hid `Map.union` Map.fromSet (const AdvApp) cur} e2
        Nothing -> printMessageCheck SevError c v (text "can only advance under delay")
    _ -> liftM2 (&&) (checkExpr c e1)  (checkExpr c e2)
checkExpr c (Case e v _ alts) =
    liftM2 (&&) (checkExpr c e) (liftM and (mapM (\ (_,vs,e)-> checkExpr (addVars vs c') e) alts))
  where c' = addVars [v] c
-- checkExpr c@Ctx{earlier = Just _} (Lam v _) =
--   printMessageCheck SevError c v (text "Functions may not be defined under delay."
--                                   $$ "In order to define a function under delay, you have to wrap it in box.")
checkExpr c (Lam v e)
  | isTyVar v || (not $ tcIsLiftedTypeKind $ typeKind $ varType v) = do
      is <- isStableConstr (varType v)
      let c' = case is of
            Nothing -> c
            Just t -> c{stableTypes = Set.insert t (stableTypes c)}
      checkExpr c' e
  | otherwise = checkExpr (addVars [v] (stabilizeLater c)) e
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
    return (and r1 && r2)  
  where vs = map fst binds
        ctxHid = maybe (current c) (Set.union (current c)) (earlier c)
        c' v = c {current = Set.empty,
                  earlier = Nothing,
                  hidden =  hidden c `Map.union`
                   (Map.fromSet (const (NestedRec v)) ctxHid),
                  recDef = recDef c `Set.union` Set.fromList vs }
checkExpr c  (Var v)
  | tcIsLiftedTypeKind $ typeKind $ varType v =  case getScope c v of
             Hidden reason -> printMessageCheck SevError c v reason
             Visible -> return True
             ImplUnboxed -> printMessageCheck SevWarning c v
                (ppr v <> text " is an external temporal function used under delay, which may cause time leaks")

  | otherwise = return True



addVars :: [Var] -> Ctx -> Ctx
addVars v c = c{current = Set.fromList v `Set.union` current c }
