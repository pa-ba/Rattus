{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}


-- | The plugin to make it all work.

module Rattus.Plugin (plugin, Rattus(..)) where
import Rattus.Plugin.StableSolver
import Rattus.Plugin.ScopeCheck
import Rattus.Plugin.Strictify
import Rattus.Plugin.Utils

import Prelude hiding ((<>))
import GhcPlugins

import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import Data.Data hiding (tyConName)

import System.Exit


-- | Use this type to mark a Haskell function definition as a Rattus
-- function:
--
-- > {-# ANN myFunction Rattus #-}
-- 
-- Or mark a whole module as consisting of Rattus functions only:
--
-- > {-# ANN module Rattus #-}
--
-- If you use the latter option, you can mark exceptions
-- (i.e. functions that should be treated as ordinary Haskell function
-- definitions) as follows:
--
-- > {-# ANN myFunction NotRattus #-}

data Rattus = Rattus | NotRattus deriving (Typeable, Data, Show, Eq)

-- | Use this to enable Rattus' plugin, either by supplying the option
-- @-fplugin=Rattus.Plugin@ directly to GHC. or by including the
-- following pragma in each source file:
-- 
-- > {-# OPTIONS -fplugin=Rattus.Plugin #-}
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install,
  tcPlugin = tcStable
  }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  return (CoreDoPluginPass "Rattus" transformProgram : todo)


transformProgram :: ModGuts -> CoreM ModGuts
transformProgram guts = do
  newBindsM <- mapM (transform guts) (mg_binds guts)
  case sequence newBindsM of
    Nothing -> liftIO exitFailure
    Just newBinds -> return $ guts { mg_binds = newBinds }


transform :: ModGuts -> CoreBind -> CoreM (Maybe CoreBind)
transform guts b@(Rec bs) = do
  tr <- liftM or (mapM (shouldTransform guts . fst) bs)
  if tr then
    case bs of
      [] -> return (Just $ Rec [])
      binds -> do
          let vs = map fst binds
          let es = map snd binds
          let vs' = Set.fromList vs
          valid <- mapM (checkExpr (emptyCtx (Just vs'))) es
          if and valid then do
            es' <- mapM strictifyExpr es
            return (Just $ Rec (zip vs es'))
          else return Nothing

  else return (Just b)
transform guts b@(NonRec v e) = do
    tr <- shouldTransform guts v
    if tr then do
      --putMsg (text "check Rattus definition: " <> ppr v)
      --putMsg (ppr e)
      valid <- checkExpr (emptyCtx Nothing) e
      if valid then do
        e' <- strictifyExpr e
        return (Just $ NonRec v e')
      else return Nothing
    else return (Just b)

getModuleAnnotations :: Data a => ModGuts -> [a]
getModuleAnnotations guts = anns'
  where anns = filter (\a-> case ann_target a of
                         ModuleTarget m -> m == (mg_module guts)
                         _ -> False) (mg_anns guts)
        anns' = mapMaybe (fromSerialized deserializeWithData . ann_value) anns
  



shouldTransform :: ModGuts -> CoreBndr -> CoreM Bool
shouldTransform guts bndr = do
  l <- annotationsOn guts bndr :: CoreM [Rattus]
  return (Rattus `elem` l && not (NotRattus `elem` l) && userFunction bndr)

annotationsOn :: (Data a) => ModGuts -> CoreBndr -> CoreM [a]
annotationsOn guts bndr = do
  anns <- getAnnotations deserializeWithData guts
  return $
    lookupWithDefaultUFM anns [] (varUnique bndr) ++
    getModuleAnnotations guts

