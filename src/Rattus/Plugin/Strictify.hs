module Rattus.Plugin.Strictify where
import Prelude hiding ((<>))
import Rattus.Plugin.Utils
import GhcPlugins


strictifyExpr :: CoreExpr -> CoreM CoreExpr
strictifyExpr (Let (NonRec b e1) e2) = do
  e1' <- strictifyExpr e1
  e2' <- strictifyExpr e2
  return (Let (NonRec b e1') e2')
strictifyExpr (Case e b t alts) = do
  e' <- strictifyExpr e
  alts' <- mapM (\(c,args,e) -> fmap (\e' -> (c,args,e')) (strictifyExpr e)) alts
  return (Case e' b t alts')
strictifyExpr (Let (Rec es) e) = do
  es' <- mapM (\ (b,e) -> strictifyExpr e >>= \e'-> return (b,e')) es
  e' <- strictifyExpr e
  return (Let (Rec es') e')
strictifyExpr (Lam b e) = do
  e' <- strictifyExpr e
  return (Lam b e')
strictifyExpr (Cast e c) = do
  e' <- strictifyExpr e
  return (Cast e' c)
strictifyExpr (Tick t e) = do
  e' <- strictifyExpr e
  return (Tick t e')
strictifyExpr e@(App e1 e2)
  | not (isType e2) && tcIsLiftedTypeKind(typeKind (exprType e2)) && not (isDelayApp e1)
    && not (isDelayApp e2) = do
  e1' <- strictifyExpr e1
  e2' <- strictifyExpr e2
  b <- mkSysLocalM (fsLit "strict") (exprType e2)
  return $ Case e2' b (exprType e) [(DEFAULT, [], App e1' (Var b))]
  | otherwise = do
  e1' <- strictifyExpr e1
  e2' <- strictifyExpr e2
  return (App e1' e2')
strictifyExpr e = return e



isDelayApp (App e _) = isDelayApp e
isDelayApp (Cast e _) = isDelayApp e
isDelayApp (Tick _ e) = isDelayApp e
isDelayApp (Var v) = isDelayVar v
isDelayApp _ = False




isDelayVar :: Var -> Bool
isDelayVar v = maybe False id $ do
  let name = varName v
  mod <- nameModule_maybe name
  let occ = getOccString name
  return ((occ == "Delay" || occ == "delay") || (occ == "Box" || occ == "delay")
          && ((moduleNameString (moduleName mod) == "Rattus.Internal") ||
          moduleNameString (moduleName mod) == "Rattus.Primitives"))

isCase Case{} = True
isCase (Tick _ e) = isCase e
isCase (Cast e _) = isCase e
isCase Lam {} = True
isCase e = isType e

isTophandler (App e1 e2) = isTophandler e1 || isTophandler e2
isTophandler (Cast e _) = isTophandler e
isTophandler (Tick _ e) = isTophandler e
isTophandler e = showSDocUnsafe (ppr e) == "GHC.TopHandler.runMainIO"

