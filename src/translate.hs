module Translate where

import Unbound.LocallyNameless
import Control.Monad.Except
import Control.Monad.Reader

import Control.Monad (liftM, liftM2, liftM3, liftM4)

import qualified Data.List as List

import Util
import qualified F
import qualified K
import qualified C

compile f = do
  af <- F.typecheck F.emptyCtx f 
  k  <- toProgK af
  K.typecheck K.emptyCtx k
  c  <- toProgC k
  C.typecheck C.emptyCtx c
  return c
  
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
toTyK (F.TyProd tys) = do  
  tys' <- mapM toTyK tys
  return $ K.TyProd tys'
  
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

    
  to (F.Ann e ty) = throwError "found nested Ann"
    
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
-- K to C
--------------------------------------------
  
type N a = ReaderT C.Ctx M a
   
toTyC :: K.Ty -> N C.Ty
toTyC (K.TyVar v) = return $ C.TyVar (translate v)
toTyC K.TyInt     = return $ C.TyInt
toTyC (K.All bnd)   = do 
  (as, tys) <- unbind bnd
  let as' = map translate as
  tys' <- local (C.extendTys as') $ mapM toTyC tys
  b' <- fresh (string2Name "b")
  let prod = C.TyProd [C.All (bind as' (C.TyVar b' : tys')), C.TyVar b']
  return $ (C.Exists (bind b' prod))
toTyC (K.TyProd tys) = do
  tys' <- mapM toTyC tys
  return $ C.TyProd tys'
  
toProgC :: K.Tm -> M C.Tm  
toProgC k = runReaderT (toTmC k) C.emptyCtx
  
toTmC :: K.Tm -> N C.Tm
toTmC (K.Let bnd) = do 
  (decl, tm) <- unbind bnd
  decl'      <- toDeclC decl
  tm'        <- local (C.extendDecl decl') (toTmC tm)
  return $ C.Let (bind decl' tm')
toTmC (K.App v@(K.Ann _ t) tys vs) = do
  -- g <- fresh $ string2Name "g"
  z <- fresh $ string2Name "z"
  zcode <- fresh $ string2Name "zcode"
  zenv <- fresh $ string2Name "zenv"
  v' <- toAnnValC v
  t' <- toTyC t
  tys' <- mapM toTyC tys
  vs'  <- mapM toAnnValC vs
  case t' of 
    C.Exists bnd -> do 
      (b, prodty) <- unbind bnd
      case prodty of 
        C.TyProd [ tcode, C.TyVar b' ] | b == b' -> do
          let vz = C.Ann (C.TmVar z) prodty
          let ds = [C.DeclUnpack b z (Embed v'), 
                    C.DeclPrj 1 zenv  (Embed vz),
                    C.DeclPrj 0 zcode (Embed vz)]
          ann <- C.mkTyApp (C.Ann (C.TmVar zcode) tcode) tys'
          let prd = (C.Ann (C.TmVar zenv) (C.TyVar b)):vs'
          return $ foldr (\ b e -> C.Let (bind b e)) (C.App ann prd) ds
        _ -> throwError "type error"
    _ -> throwError "type error"
toTmC (K.TmIf0 v tm1 tm2) = do    
  liftM3 C.TmIf0 (toAnnValC v) (toTmC tm1) (toTmC tm2)
toTmC (K.Halt ty v) =
  liftM2 C.Halt (toTyC ty) (toAnnValC v)
    
toDeclC :: K.Decl -> N C.Decl
toDeclC (K.DeclVar   x (Embed v)) = do
  v' <- toAnnValC v
  return $ C.DeclVar (translate x) (Embed v')
toDeclC (K.DeclPrj i x (Embed v)) = do
  v' <- toAnnValC v
  return $ C.DeclPrj i (translate x) (Embed v')
toDeclC (K.DeclPrim  x (Embed (v1, p, v2))) = do
  v1' <- toAnnValC v1
  v2' <- toAnnValC v2
  return $ C.DeclPrim (translate x) (Embed (v1',p, v2'))

toAnnValC :: K.AnnVal -> N C.AnnVal
toAnnValC (K.Ann (K.TmInt i) K.TyInt) = 
  return $ C.Ann (C.TmInt i) C.TyInt
toAnnValC (K.Ann (K.TmVar v) ty) = do
  ty' <- toTyC ty
  return $ C.Ann (C.TmVar (translate v)) ty'
toAnnValC (K.Ann v@(K.Fix bnd1) t@(K.All _)) = do
  t' <- toTyC t
  ((f,as), bnd2)  <- unbind bnd1
  (xtys, e)       <- unbind bnd2
  let (xs,tys) = unzip $ map (\(x,Embed ty) -> (x,ty)) xtys
  let xs'  = map translate xs
  tys'     <- mapM toTyC tys
  let ys   = (map translate (List.nub (fv v :: [K.ValName])))
  ctx      <- ask
  ss'      <- lift $ mapM (C.lookupTmVar ctx) ys            
  let as'  = map translate as
  let bs   = (map translate (List.nub (fv v :: [K.TyName])))
  let tenv     = C.TyProd ss'
  let trawcode = C.All (bind (bs ++ as') (tenv:tys'))
  zvar         <- fresh $ string2Name "zfix"
  let zcode    = C.Ann (C.TmVar zvar) trawcode
  zenvvar      <- fresh $ string2Name "zfenv"      
  let zenv     = C.Ann (C.TmVar zenvvar) tenv
  tyAppZenv <- C.mkTyApp zcode (map C.TyVar bs)

  let mkprj (x, i) e = 
        C.Let (bind (C.DeclPrj i x (Embed zenv)) e)        
  let extend = \c -> foldr (uncurry C.extendTm) c (zip xs' tys')
  e' <- local (C.extendTm (translate f) t' . extend) $ toTmC e
  let vcode    = C.Fix (bind (zvar, (bs ++ as'))
                        (bind ((zenvvar, Embed tenv): 
                               zipWith (\x ty -> (x,Embed ty)) xs' tys')
                         (C.Let (bind (C.DeclVar (translate f)
                                       (Embed (C.Ann (C.Pack tenv (C.mkProd [tyAppZenv, zenv]))
                                               t')))
                                 (foldr mkprj e' (zip ys [0..]))))))
  let venv     = C.mkProd (zipWith (\y ty -> C.Ann (C.TmVar y) ty) ys ss')
  tyAppVcode <- (C.mkTyApp (C.Ann vcode trawcode) (map C.TyVar bs))
  return $
    C.Ann (C.Pack tenv (C.mkProd [tyAppVcode, venv])) t'

toAnnValC (K.Ann (K.TmProd vs) ty) = do
  ty' <- toTyC ty
  vs' <- mapM toAnnValC vs
  return $ C.Ann (C.TmProd vs') ty'
