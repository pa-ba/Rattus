{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}


-- | The plugin to make it all work.

module Rattus.Plugin (plugin, Rattus(..)) where
import Rattus.Plugin.StableSolver
import Rattus.Plugin.ScopeCheck
import Rattus.Plugin.Strictify
import Rattus.Plugin.Utils
import Rattus.Plugin.Annotation

import Prelude hiding ((<>))
import GhcPlugins
import TcRnTypes


import Control.Monad
import Data.Maybe
import Data.Data hiding (tyConName)




-- | Use this to enable Rattus' plugin, either by supplying the option
-- @-fplugin=Rattus.Plugin@ directly to GHC. or by including the
-- following pragma in each source file:
-- 
-- > {-# OPTIONS -fplugin=Rattus.Plugin #-}
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install,
  pluginRecompile = purePlugin,
  typeCheckResultAction = typechecked,
  tcPlugin = tcStable
  }


typechecked :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
typechecked _ _ env = checkAll env >> return env

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = return (strPass : todo)
    where strPass = CoreDoPluginPass "Rattus strictify" strictifyProgram

strictifyProgram :: ModGuts -> CoreM ModGuts
strictifyProgram guts = do
  newBinds <- mapM (strictify guts) (mg_binds guts)
  return guts { mg_binds = newBinds }

strictify :: ModGuts -> CoreBind -> CoreM (CoreBind)
strictify guts b@(Rec bs) = do
  tr <- liftM or (mapM (shouldTransform guts . fst) bs)
  if tr then do
    let vs = map fst bs
    es' <- mapM (\ (v,e) -> do
                    lazy <- allowLazyData guts v
                    strictifyExpr (SCxt (nameSrcSpan $ getName v) (not lazy))e) bs
    return (Rec (zip vs es'))
  else return b
strictify guts b@(NonRec v e) = do
    tr <- shouldTransform guts v
    if tr then do
      lazy <- allowLazyData guts v
      e' <- strictifyExpr (SCxt (nameSrcSpan $ getName v) (not lazy)) e
      return (NonRec v e')
    else return b

getModuleAnnotations :: Data a => ModGuts -> [a]
getModuleAnnotations guts = anns'
  where anns = filter (\a-> case ann_target a of
                         ModuleTarget m -> m == (mg_module guts)
                         _ -> False) (mg_anns guts)
        anns' = mapMaybe (fromSerialized deserializeWithData . ann_value) anns
  



allowLazyData :: ModGuts -> CoreBndr -> CoreM Bool
allowLazyData guts bndr = do
  l <- annotationsOn guts bndr :: CoreM [Rattus]
  return (AllowLazyData `elem` l)


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

