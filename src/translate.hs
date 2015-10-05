module Translate where

import Unbound.LocallyNameless
import Control.Monad.Trans.Except

import Util
import qualified F
import qualified K

compile f = do
  af <- F.typecheck F.emptyCtx f 
  k  <- toProgK af
  K.typecheck K.emptyCtx k
  return k
  
--------------------------------------------
-- F ==> K
--------------------------------------------
  
-- type translation  
  
toTyK :: F.Ty -> M K.Ty
toTyK (F.TyVar n) = return $ K.TyVar (translate n)
toTyK F.TyInt     = return $ K.TyInt
toTyK (F.Arr t1 t2) = do
  k1     <- toTyK t1
  k2     <- toTyContK t2
  return $ K.All (bind [] [k1,k2])
toTyK (F.All bnd) = do 
  (a,ty) <- unbind bnd
  let a' = translate a
  ty'    <- toTyContK ty
  return $ K.All (bind [a'][ty'])
toTyContK fty = do
  kty    <- toTyK fty
  return $ K.All (bind [] [kty])
  
-- expression translation
  
-- Here we actually use Danvy & Filinski's "optimizing" closure-conversion
-- algorithm.  It is actually no more complicated than the one presented in  
-- the paper and produces output with no "administrative" redices.

toProgK :: F.Tm -> M K.Tm
toProgK ae@(F.Ann ftm fty) = do
  kty   <- toTyK fty             
  toExpK ae (\kv -> return $ K.Halt kty kv)

  
toExpK :: F.Tm -> (K.AnnVal -> M K.Tm) -> M K.Tm
toExpK (F.Ann ftm fty) k = to ftm where
    
  to (F.TmVar y) = do 
    kty <- toTyK fty
    k (K.Ann (K.TmVar (translate y)) kty)
    
  to (F.TmInt i) = k (K.Ann (K.TmInt i) K.TyInt)
  
  to (F.Fix bnd) = do 
    ((f, x, Embed (t1,t2)), e) <- unbind bnd
    kty1  <- toTyK t1
    kcty2 <- toTyContK t2
    kvar  <- fresh (string2Name "k")
    ke    <- toExpK e (\v -> return $ K.App (K.Ann (K.TmVar kvar) kcty2) [] [v])
    let kfix  = K.Fix (bind (translate f, []) 
                       (bind [(translate x, Embed kty1),(kvar, Embed kcty2)] 
                        ke))
    k (K.Ann kfix (K.All (bind [] [kty1,kcty2])))
    
  to (F.App ae1 ae2) = do
    kty  <- toTyK fty
    let body v1 v2 = do
          kv <- reifyCont k kty           
          return (K.App v1 [] [v2, kv])
    toExpK ae1 (\v1 -> toExpK ae2 (\v2 -> body v1 v2))

  to (F.TmPrim ae1 p ae2) = do
    y <- fresh (string2Name "y")
    let body v1 v2 = do
          tm <- k (K.Ann (K.TmVar y) K.TyInt)
          return (K.Let (bind (K.DeclPrim y (Embed (v1,p, v2))) tm))
    toExpK ae1 (\ x1 -> toExpK ae2 (body x1))
    
  to (F.TmIf0 ae0 ae1 ae2) = do
    e1 <- toExpK ae1 k
    e2 <- toExpK ae2 k
    toExpK ae0 (\v1 -> return (K.TmIf0 v1 e1 e2))
    
  to (F.TmProd aes) = do 
    kty <- toTyK fty
    let loop [] k = k []
        loop (ae:aes) k = 
           toExpK ae (\v -> loop aes (\vs -> k (v:vs)))
    loop aes (\vs -> k (K.Ann (K.TmProd vs) kty))
    
  to (F.TmPrj ae i) = do
    y   <- fresh (string2Name "y")
    yty <- toTyK fty
    toExpK ae (\ v1 -> do
                  tm <- k (K.Ann (K.TmVar y) yty)
                  return (K.Let (bind (K.DeclPrj i y (Embed v1)) tm)))
      
  to (F.TLam bnd) = do
      (a,e@(F.Ann _ ty)) <- unbind bnd
      kcty <- toTyContK ty
      kvar <- fresh (string2Name "k")
      ke   <- toExpK e (\v -> return $ K.App (K.Ann (K.TmVar kvar) kcty) [] [v])
      f    <- fresh (string2Name "f")
      let kfix  = K.Fix (bind (f, [translate a]) 
                         (bind [(kvar, Embed kcty)] ke))
      k (K.Ann kfix (K.All (bind [translate a] [kcty])))

  to (F.TApp ae ty) = do
    aty  <- toTyK ty
    let body v1 = do
          kty  <- toTyK fty
          kv <- reifyCont k kty           
          return (K.App v1 [aty] [kv])
    toExpK ae body

    
  to (F.Ann e ty) = throwE "found nested Ann"
    
-- Turn a meta continuation into an object language continuation    
-- Requires knowing the type of the expected value.
    
reifyCont :: (K.AnnVal -> M K.Tm) -> K.Ty -> M K.AnnVal
reifyCont k vty = do
  kont <- fresh (string2Name "kont")  
  v    <- fresh (string2Name "v")
  body <- k (K.Ann (K.TmVar v) vty) 
  return $ K.Ann (K.Fix (bind (kont, []) 
                         (bind [(v, Embed vty)] body)))
                 (K.All (bind [][vty]))
     
--------------------------------------------
-- 
--------------------------------------------
   
    
