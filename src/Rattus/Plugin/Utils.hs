{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Rattus.Plugin.Utils (
  printMessage,
  Severity(..),
  isRattModule,
  isGhcModule,
  getNameModule,
  isStable,
  isTemporal,
  userFunction,
  isType)
  where

import ErrUtils
import Prelude hiding ((<>))
import GhcPlugins
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char

isType Type {} = True
isType (App e _) = isType e
isType (Cast e _) = isType e
isType (Tick _ e) = isType e
isType _ = False



-- printMessage :: Severity -> SDoc -> CoreM ()
-- printMessage sev doc =
--   case sev of
--     Error -> errorMsg doc
--     Warning -> warnMsg doc


-- printMessageV :: Severity -> Var -> SDoc -> CoreM ()
-- printMessageV sev var doc =
--   let loc = nameSrcLoc (varName var)
--       doc' = ppr loc <> text ": " <> doc
--   in case sev of
--     Error -> errorMsg doc'
--     Warning -> warnMsg doc'


printMessage :: Severity -> SrcSpan -> SDoc -> CoreM ()
printMessage sev loc doc = do
  dflags <- getDynFlags
  unqual <- getPrintUnqualified
  let sty = case sev of
                     SevError   -> err_sty
                     SevWarning -> err_sty
                     SevDump    -> dump_sty
                     _          -> user_sty
      err_sty  = mkErrStyle dflags unqual
      user_sty = mkUserStyle dflags unqual AllTheWay
      dump_sty = mkDumpStyle dflags unqual
  liftIO $ putLogMsg dflags NoReason sev loc sty doc



rattModules :: Set FastString
rattModules = Set.fromList ["Rattus.Internal","Rattus.Primitives"
                           ,"Rattus.Stable", "Rattus.Arrow"]

isRattModule :: FastString -> Bool
isRattModule = (`Set.member` rattModules)

isGhcModule :: FastString -> Bool
isGhcModule = (== "GHC.Types")


getNameModule :: NamedThing a => a -> Maybe (FastString, FastString)
getNameModule v = do
  let name = getName v
  mod <- nameModule_maybe name
  return (getOccFS name,moduleNameFS (moduleName mod))


-- | The set of stable built-in types.
ghcStableTypes :: Set FastString
ghcStableTypes = Set.fromList ["Int","Bool","Float","Double","Char"]


newtype TypeCmp = TC Type

instance Eq TypeCmp where
  (TC t1) == (TC t2) = eqType t1 t2

instance Ord TypeCmp where
  compare (TC t1) (TC t2) = nonDetCmpType t1 t2

isTemporal :: Type -> Bool
isTemporal t = isTemporalRec 0 Set.empty t


isTemporalRec :: Int -> Set TypeCmp -> Type -> Bool
isTemporalRec d _ _ | d == 100 = False
isTemporalRec _ pr t | Set.member (TC t) pr = False
isTemporalRec d pr t = do
  let pr' = Set.insert (TC t) pr
  case splitTyConApp_maybe t of
    Nothing -> False
    Just (con,args) ->
      case getNameModule con of
        Nothing -> False
        Just (name,mod)
          -- If it's a Rattus type constructor check if it's a box
          | isRattModule mod && (name == "Box" || name == "O") -> True
          | isFunTyCon con -> or (map (isTemporalRec (d+1) pr') args)
          | isAlgTyCon con -> 
            case algTyConRhs con of
              DataTyCon {data_cons = cons} -> or (map check cons)
                where check con = case dataConInstSig con args of
                        (_, _,tys) -> or (map (isTemporalRec (d+1) pr') tys)
              _ -> or (map (isTemporalRec (d+1) pr') args)
        _ -> False


-- | Check whether the given type is stable. This check may use
-- 'Stable' constraints from the context.

isStable :: Set Var -> Type -> Bool
isStable c t = isStableRec c 0 Set.empty t

-- | Check whether the given type is stable. This check may use
-- 'Stable' constraints from the context.

isStableRec :: Set Var -> Int -> Set TypeCmp -> Type -> Bool
-- To prevent infinite recursion (when checking recursive types) we
-- keep track of previously checked types. This, however, is not
-- enough for non-regular data types. Hence we also have a counter.
isStableRec _ d _ _ | d == 100 = True
isStableRec _ _ pr t | Set.member (TC t) pr = True
isStableRec c d pr t = do
  let pr' = Set.insert (TC t) pr
  case splitTyConApp_maybe t of
    Nothing -> case getTyVar_maybe t of
      Just v -> -- if it's a type variable, check the context
        v `Set.member` c
      Nothing -> False
    Just (con,args) ->
      case getNameModule con of
        Nothing -> False
        Just (name,mod)
          -- If it's a Rattus type constructor check if it's a box
          | isRattModule mod && name == "Box" -> True
            -- If its a built-in type check the set of stable built-in types
          | isGhcModule mod -> name `Set.member` ghcStableTypes
          {- deal with type synonyms (does not seem to be necessary (??))
           | Just (subst,ty,[]) <- expandSynTyCon_maybe con args ->
             isStableRec c (d+1) pr' (substTy (extendTvSubstList emptySubst subst) ty) -}
          | isAlgTyCon con -> 
            case algTyConRhs con of
              DataTyCon {data_cons = cons, is_enum = enum}
                | enum -> True
                | and $ concatMap (map isSrcStrict'
                                   . dataConSrcBangs) $ cons ->
                  and  (map check cons)
                | otherwise -> False
                where check con = case dataConInstSig con args of
                        (_, _,tys) -> and (map (isStableRec c (d+1) pr') tys)
              TupleTyCon {} -> null args
              _ -> False
        _ -> False


          
isSrcStrict' (HsSrcBang _ _ SrcStrict) = True
isSrcStrict' _ = False


userFunction :: Var -> Bool
userFunction v =
  case getOccString (getName v) of
    (c : _)
      | isUpper c || c == '$' || c == ':' -> False
      | otherwise -> True
    _ -> False
