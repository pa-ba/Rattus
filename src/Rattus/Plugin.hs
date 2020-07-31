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

data Rattus = Rattus | NotRattus | AllowLazyData deriving (Typeable, Data, Show, Eq)

-- | Use this to enable Rattus' plugin, either by supplying the option
-- @-fplugin=Rattus.Plugin@ directly to GHC. or by including the
-- following pragma in each source file:
-- 
-- > {-# OPTIONS -fplugin=Rattus.Plugin #-}
plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install,
  tcPlugin = tcStable,
  pluginRecompile = purePlugin
  }



install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = return (scPass : strPass : todo)
    where scPass = CoreDoPluginPass "Rattus scopecheck" scopecheckProgram

          strPass = CoreDoPluginPass "Rattus strictify" strictifyProgram

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


scopecheckProgram :: ModGuts -> CoreM ModGuts
scopecheckProgram guts = do
  res <- mapM (scopecheck guts) (mg_binds guts)
  if and res then return guts else liftIO exitFailure


scopecheck :: ModGuts -> CoreBind -> CoreM Bool
scopecheck guts (Rec bs) = do
  tr <- liftM or (mapM (shouldTransform guts . fst) bs)
  if tr then do
    let vs = map fst bs
    let vs' = Set.fromList vs
    valid <- mapM (\ (v,e) -> checkExpr (emptyCtx (Just vs') v) e) bs
    return (and valid)
  else return True
scopecheck guts (NonRec v e) = do
    tr <- shouldTransform guts v
    if tr then do
      valid <- checkExpr (emptyCtx Nothing v) e
      return valid
    else return True

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

