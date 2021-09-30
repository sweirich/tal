
module Translate where

import Unbound.Generics.LocallyNameless hiding (to)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.PermM ( single )

import Debug.Trace

import Util
import qualified F
import qualified K
import qualified C
import qualified A
import qualified TAL

-- Not sure the right way to do this. But a is a Phantom type in 
-- unbound generics
translate :: Name a -> Name b
translate n = makeName s i where 
  (s,i) = (name2String n, name2Integer n)

------------------------------------
-- The compiler pipeline, all passes
------------------------------------

compile :: F.Tm -> M TAL.Machine
compile f = do
  af <- F.typecheck F.emptyCtx f
  k  <- toProgK af
  K.typecheck K.emptyCtx k
  c  <- toProgC k
  C.typecheck C.emptyCtx c
  h <- toProgH c
  C.hoistcheck h
  a <- toProgA h
  A.progcheck a
  tal <- toProgTAL a
  TAL.progcheck tal
  return tal


--------------------------------------------
-- F ==> K
--------------------------------------------

-- type translation


toTyK :: F.Ty -> M K.Ty
toTyK (F.TyVar n) = return $ K.TyVar (translate n)
toTyK F.TyInt     = return K.TyInt
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

toTyContK :: F.Ty -> M K.Ty
toTyContK fty = do
  kty    <- toTyK fty
  return $ K.All (bind [] [kty])

-- expression translation

-- Here we actually use Danvy & Filinski's "optimizing" closure-conversion
-- algorithm.  It is actually no more complicated than the one presented in
-- the paper and produces output with no "administrative" redices.

toProgK :: F.Tm -> M K.Tm
toProgK ae@(F.Ann _ fty) = do
  kty   <- toTyK fty
  toExpK ae (return . K.Halt kty)
toProgK _ = throwError "toProgK given unannotated expression!"

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
    toExpK ae1 (toExpK ae2 . body)

  to (F.TmPrim ae1 p ae2) = do
    y <- fresh (string2Name "y")
    let body v1 v2 = do
          tm <- k (K.Ann (K.TmVar y) K.TyInt)
          return (K.Let (bind (K.DeclPrim y (Embed (v1,p, v2))) tm))
    toExpK ae1 (toExpK ae2 . body)

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
      (a,e) <- unbind bnd
      case e of 
        F.Ann _ ty -> do
          kcty <- toTyContK ty
          kvar <- fresh (string2Name "k")
          ke   <- toExpK e (\v -> return $ K.App (K.Ann (K.TmVar kvar) kcty) [] [v])
          f    <- fresh (string2Name "f")
          let kfix  = K.Fix (bind (f, [translate a])
                            (bind [(kvar, Embed kcty)] ke))
          k (K.Ann kfix (K.All (bind [translate a] [kcty])))
        _ -> throwError "toExpK: need annotation"
  to (F.TApp ae ty) = do
    aty  <- toTyK ty
    let body v1 = do
          kty  <- toTyK fty
          kv <- reifyCont k kty
          return (K.App v1 [aty] [kv])
    toExpK ae body


  to (F.Ann e ty) = throwError "found nested Ann"
toExpK _ _ = throwError "toExpK: found unannotated expression"


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
-- K to C    Closure conversion
--------------------------------------------

-- NOTE: we need to keep track of the current context
-- so that we can find out the types of free variables
-- (The FV function only gives us free names, not free
-- annotated variables)
type N a = ReaderT C.Ctx M a

toTyC :: K.Ty -> N C.Ty
toTyC (K.TyVar v) = return $ C.TyVar (translate v)
toTyC K.TyInt     = return C.TyInt
toTyC (K.All bnd)   = do
  (as, tys) <- unbind bnd
  let as' = map translate as
  tys' <- local (C.extendTys as') $ mapM toTyC tys
  b' <- fresh (string2Name "b")
  let prod = C.TyProd [C.All (bind as' (C.TyVar b' : tys')), C.TyVar b']
  return (C.Exists (bind b' prod))
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
  z     <- fresh $ string2Name "z"
  zcode <- fresh $ string2Name "zcode"
  zenv  <- fresh $ string2Name "zenv"
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
          let prd = C.Ann (C.TmVar zenv) (C.TyVar b):vs'
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
  let ys   = map translate (List.nub (toListOf fv v :: [K.ValName]))
  ctx      <- ask
  ss'      <- lift $ mapM (C.lookupTmVar ctx) ys
  let as'  = map translate as
  let bs   = map translate (List.nub (toListOf fv v :: [K.TyName]))
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
  let vcode    = C.Fix (bind (zvar, bs ++ as')
                        (bind ((zenvvar, Embed tenv):
                               zipWith (\x ty -> (x,Embed ty)) xs' tys')
                         (C.Let (bind (C.DeclVar (translate f)
                                       (Embed (C.Ann (C.Pack tenv (C.mkProd [tyAppZenv, zenv]))
                                               t')))
                                 (foldr mkprj e' (zip ys [0..]))))))
  let venv     = C.mkProd (zipWith (C.Ann . C.TmVar) ys ss')
  tyAppVcode <- C.mkTyApp (C.Ann vcode trawcode) (map C.TyVar bs)
  return $
    C.Ann (C.Pack tenv (C.mkProd [tyAppVcode, venv])) t'

toAnnValC (K.Ann (K.TmProd vs) ty) = do
  ty' <- toTyC ty
  vs' <- mapM toAnnValC vs
  return $ C.Ann (C.TmProd vs') ty'
toAnnValC _ = throwError "toAnnValC: inconsistent annotation"

--------------------------------------------
-- C to H  (actually C)  Hoisting
--------------------------------------------

-- we keep track of the current heap as we hoist
-- 'fix' expressions out of expressions
type H a = StateT C.Heap M a

toProgH :: C.Tm -> M (C.Tm, C.Heap)
toProgH tm = runStateT (toTmH tm) mempty

toTmH :: C.Tm -> H C.Tm
toTmH (C.Let bnd) = do
  (decl, tm) <- unbind bnd
  decl'      <- toDeclH decl
  tm'        <- toTmH tm
  return $ C.Let (bind decl' tm')
toTmH (C.App v vs) = do
  v'   <- toAnnValH v
  vs'  <- mapM toAnnValH vs
  return $ C.App v' vs'
toTmH (C.TmIf0 v tm1 tm2) = do
  liftM3 C.TmIf0 (toAnnValH v) (toTmH tm1) (toTmH tm2)
toTmH (C.Halt ty v) =
  C.Halt ty <$> toAnnValH v

toDeclH :: C.Decl -> H C.Decl
toDeclH (C.DeclVar x (Embed v)) = do
  v' <- toAnnValH v
  return $ C.DeclVar x (Embed v')
toDeclH (C.DeclPrj i x (Embed v)) = do
  v' <- toAnnValH v
  return $ C.DeclPrj i x (Embed v')
toDeclH (C.DeclPrim  x (Embed (v1, p, v2))) = do
  v1' <- toAnnValH v1
  v2' <- toAnnValH v2
  return $ C.DeclPrim x (Embed (v1',p, v2'))
toDeclH (C.DeclUnpack g x (Embed v)) = do
  v' <- toAnnValH v
  return $ C.DeclUnpack g x (Embed v')


toAnnValH :: C.AnnVal -> H C.AnnVal
toAnnValH (C.Ann (C.TmInt i) _) =
  return $ C.Ann (C.TmInt i) C.TyInt
toAnnValH (C.Ann (C.TmVar v) ty) = do
  return $ C.Ann (C.TmVar v) ty
toAnnValH (C.Ann (C.Fix bnd1) ty) = do
  ((f, as),bnd2)  <- unbind bnd1
  (xtys, tm)      <- unbind bnd2
  codef           <- fresh f
  tm'             <- toTmH tm
  let v' = C.Ann (C.Fix (bind (f,as) (bind xtys tm'))) ty
  modify (\s -> mappend s (C.Heap (Map.singleton codef v')))
  return (C.Ann (C.TmVar codef) ty)

toAnnValH (C.Ann (C.TmProd ps) ty) = do
  ps' <- mapM toAnnValH ps
  return $ C.Ann (C.TmProd ps') ty
toAnnValH (C.Ann (C.TApp v ty1) ty) = do
  v' <- toAnnValH v
  return $ C.Ann (C.TApp v' ty1) ty
toAnnValH (C.Ann (C.Pack ty1 v) ty) = do
  v' <- toAnnValH v
  return $ C.Ann (C.Pack ty1 v') ty

--------------------------------------------
-- H to A  (Allocation)
--------------------------------------------

toTyA :: C.Ty -> M A.Ty
toTyA (C.TyVar v) = return $ A.TyVar (translate v)
toTyA C.TyInt     = return A.TyInt
toTyA (C.All bnd)   = do
  (as, tys) <- unbind bnd
  let as' = map translate as
  tys' <- mapM toTyA tys
  return (A.All (bind as' tys'))
toTyA (C.TyProd tys) = do
  tys' <- mapM toTyA tys
  return $ A.TyProd $ map (,A.Init) tys'
toTyA (C.Exists bnd) = do
  (a, ty) <- unbind bnd
  let a' = translate a
  ty' <- toTyA ty
  return $ A.Exists (bind a' ty')

toProgA :: (C.Tm, C.Heap) -> M (A.Tm, A.Heap)
toProgA (tm, C.Heap heap) = do
  asc <- mapM (\(x,hv) -> let x' = translate x in
                (x',) <$> toHeapValA x' hv)
         (Map.assocs heap)
  let heap' = A.Heap (Map.fromDistinctAscList asc)
  tm' <- toExpA tm
  return (tm', heap')

toHeapValA :: A.ValName -> C.AnnVal -> M (A.Ann A.HeapVal)
toHeapValA f' (C.Ann (C.Fix bnd) _) = do
  ((f,as), bnd2) <- unbind bnd
  (xtys, e)      <- unbind bnd2
  let 
     f1 :: C.ValName
     f1 = translate f'
  let e' = swaps (single (AnyName f1)(AnyName f)) e
  let (xs,tys) = unzip $ map (\(x,Embed y) -> (x,y)) xtys
  tys' <- mapM toTyA tys
  let as' = map translate as
  let xs' = map translate xs
  e'' <- toExpA e'
  return (A.Ann (A.Code (bind as' (bind xs' e''))) (A.All (bind as' tys')))
toHeapValA _ _ = throwError "only code in the heap"


toExpA :: C.Tm -> M A.Tm
toExpA (C.Let bnd)  = do
  (d, tm) <- unbind bnd
  ds' <- toDeclA d
  tm' <- toExpA tm
  return $ A.lets ds' tm'
toExpA (C.App av avs) = do
  (ds', av') <- toAnnValA av
  dsav <- mapM toAnnValA avs
  let (dss, avs') = unzip dsav
  return $ A.lets (ds' ++ concat dss) (A.App av' avs')
toExpA (C.TmIf0 av e1 e2) = do
  (ds', av') <- toAnnValA av
  e1' <- toExpA e1
  e2' <- toExpA e2
  return $ A.lets ds' (A.TmIf0 av' e1' e2')
toExpA (C.Halt ty av) = do
  ty' <- toTyA ty
  (ds', av') <- toAnnValA av
  return (A.lets ds' (A.Halt ty' av'))


toDeclA :: C.Decl -> M [A.Decl]
toDeclA (C.DeclVar x (Embed av)) = do
  (ds', av') <- toAnnValA av
  return (ds' ++ [A.DeclVar (translate x) (Embed av')])
toDeclA (C.DeclPrj i x (Embed av)) = do
  (ds', av') <- toAnnValA av
  return (ds' ++ [A.DeclPrj i (translate x) (Embed av')])
toDeclA (C.DeclPrim x (Embed (av1,p,av2))) = do
  (ds1', av1') <- toAnnValA av1
  (ds2', av2') <- toAnnValA av2
  return (ds1' ++ ds1' ++ [A.DeclPrim (translate x)
                           (Embed (av1', p, av2'))])

toDeclA (C.DeclUnpack a x (Embed av)) = do
  (ds', av') <- toAnnValA av
  return (ds' ++ [A.DeclUnpack (translate a) (translate x)
                 (Embed av')])

-- create the type  [ ty_0^1 ... ty_{i-1}^1 ty_i^0 ty_{i+1}^0 ...]
updateProd :: [A.Ty] -> Int -> [(A.Ty,A.Flag)]
updateProd tys i = [ (ty, if j < i then A.Init else A.Un) |
                     (ty, j) <- zip tys [0..] ]



toAnnValA :: C.AnnVal -> M ([A.Decl],A.Ann A.Val)
toAnnValA (C.Ann (C.TmProd vs) (C.TyProd tys)) = do
  dvs' <- mapM toAnnValA vs
  let (dss', vs') = unzip dvs'
  tys' <- mapM toTyA tys
  y <- fresh $ string2Name "ym"
  -- combine helper function for initialization
  -- y   -- name of tuple to initialize
  --     -- typle type [ ty_0^1 ... ty_{i-1}^1 ty_i^0 ...]
  -- ds  -- current list of declarations
  -- i   -- index of the tuple to initialize
  -- avi -- value initialize y[i]
  let initialize tys' (yt, ds) (i,avi) = do
        y1 <- fresh $ string2Name "ya"
        let ay0 = A.Ann (A.TmVar yt) (A.TyProd (updateProd tys' i))
        return (y1, ds ++ [A.DeclAssign y1 (Embed (ay0, i, avi))])
  (yn, ds') <- foldM (initialize tys')
               (y, concat dss' ++ [A.DeclMalloc y (Embed tys')])
               (zip [0..] vs')
  return (ds', A.Ann (A.TmVar yn) (A.TyProd (map (,A.Init) tys')))


toAnnValA (C.Ann v ty) = do
  (d,v')  <- toValA v
  ty' <- toTyA ty
  return (d, A.Ann v' ty')

toValA :: C.Val -> M ([A.Decl],A.Val)
toValA (C.TmInt i) = return ([], A.TmInt i)
toValA (C.TmVar v) = return ([], A.TmVar (translate v))
toValA (C.TApp av ty) = do
  (ds', av') <- toAnnValA av
  ty' <- toTyA ty
  return (ds', A.TApp av' ty')
toValA (C.Pack ty av) = do
  ty' <- toTyA ty
  (ds', av') <- toAnnValA av
  return (ds', A.Pack ty' av')
toValA (C.Fix _) = throwError "no fix after hoist"
toValA (C.TmProd _) = throwError "catch in Annval"

--------------------------------------------
-- A to TAL  (Code Generation)
--------------------------------------------

toFlag :: A.Flag -> TAL.Flag
toFlag A.Init = TAL.Init
toFlag A.Un   = TAL.Un

toTyTAL :: A.Ty -> M TAL.Ty
toTyTAL (A.TyVar v) = return $ TAL.TyVar (translate v)
toTyTAL A.TyInt     = return TAL.TyInt
toTyTAL (A.All bnd)   = do
  (as, tys) <- unbind bnd
  let as' = map translate as
  tys' <- mapM toTyTAL tys
  let gamma = zip [TAL.reg1 ..] tys'
  return (TAL.All (bind as' gamma))
toTyTAL (A.TyProd tys) = do
  tys' <- mapM (\(ty,f) -> (,toFlag f) <$> toTyTAL ty) tys
  return $ TAL.TyProd tys'
toTyTAL (A.Exists bnd) = do
  (a, ty) <- unbind bnd
  let a' = translate a
  ty' <- toTyTAL ty
  let ty2 = TAL.Exists $ bind a' ty'
  return $ TAL.Exists (bind a' ty')

-- Keep track of the mapping between variables and registers
-- or heap locations
type Varmap = Map A.ValName TAL.SmallVal

-- Create a register corresponding to a particular
-- value variable
var2reg :: A.ValName -> M (TAL.Register, Varmap)
var2reg x = let rd = TAL.Register ("r" ++ name2String x ++ show (name2Integer x)) in
  return (rd,Map.singleton x (TAL.RegVal rd))


toSmallVal :: Varmap -> A.Ann A.Val -> M (TAL.SmallVal, TAL.Ty)
toSmallVal vm (A.Ann (A.TmInt i) _) =
  return (TAL.WordVal (TAL.TmInt i), TAL.TyInt)
toSmallVal vm (A.Ann (A.TmVar x) ty) = do
  ty' <- toTyTAL ty
  case Map.lookup x vm of
    Just sv -> return (sv, ty')
    Nothing -> throwError $ show x ++ " not found"
toSmallVal vm (A.Ann (A.TApp av ty) ty1)    = do
  ty1' <- toTyTAL ty1
  ty' <- toTyTAL ty
  (sv',_) <- toSmallVal vm av
  return (TAL.SApp (TAL.TyApp sv' ty'), ty1')
toSmallVal vm (A.Ann (A.Pack ty1 av) ty2) = do
  ty1' <- toTyTAL ty1
  (av', _)  <- toSmallVal vm av
  ty2' <- toTyTAL ty2
  return (TAL.SPack (TAL.Pack ty1' av' ty2'), ty2')

toWordVal :: Varmap -> A.Ann A.Val -> M TAL.WordVal
toWordVal vm (A.Ann (A.TmInt i) _) = return $ TAL.TmInt i
toWordVal vm (A.Ann (A.TmVar x) _) = case Map.lookup x vm of
  Just (TAL.WordVal wv) -> return wv
  Just _  -> throwError "must be wordval"
  Nothing -> throwError "not found"
toWordVal vm (A.Ann (A.TApp av ty) _)    = do
  ty' <- toTyTAL ty
  sv' <- toWordVal vm av
  return $ TAL.WApp (TAL.TyApp sv' ty')
toWordVal vm (A.Ann (A.Pack ty1 av) ty2) = do
  ty1' <- toTyTAL ty1
  av'  <- toWordVal vm av
  ty2' <- toTyTAL ty2
  return $ TAL.WPack (TAL.Pack ty1' av' ty2')


toInstrsTAL :: Varmap -> TAL.Delta -> TAL.Gamma -> A.Tm
               -> M (TAL.Heap, TAL.InstrSeq)
toInstrsTAL vm delta gamma (A.Let bnd) = do
  (decl, tm) <- unbind bnd
  (vm', delta', gamma', is) <- toDeclTAL vm delta gamma decl
  (heap, is') <- toInstrsTAL vm' delta' gamma' tm
  return (heap, foldr TAL.Seq is' is)
toInstrsTAL vm delta gamma (A.App av args) = do
  (sv, _) <- toSmallVal vm av
  (svs,_) <- unzip <$> mapM (toSmallVal vm) args
  let rtmps = zipWith (\ i _ -> TAL.rtmp i) [1 .. ] svs
  let movs1 = zipWith TAL.Mov rtmps svs
  let movs2 = zipWith TAL.Mov [TAL.reg1 ..]
              (map TAL.RegVal rtmps)
  return (Map.empty,
          foldr TAL.Seq
          (TAL.Jump (TAL.RegVal (TAL.rtmp 0)))
          ([TAL.Mov (TAL.rtmp 0) sv] ++ movs1 ++ movs2))

toInstrsTAL vm delta gamma (A.TmIf0 av e1 e2) = do
  (sv,_)   <- toSmallVal vm av
  (h1,is1) <- toInstrsTAL vm delta gamma e1
  (h2,is2) <- toInstrsTAL vm delta gamma e2
  l        <- TAL.Label <$> fresh (string2Name "l")
  let h = Map.singleton l (TAL.Code (map translate delta) gamma is2)
  return (Map.unions [h1,h2, h],
          TAL.Mov (TAL.rtmp 0) sv `TAL.Seq`
          (TAL.Bnz (TAL.rtmp 0)
            (TAL.sapps (TAL.WordVal (TAL.LabelVal l))
                       (map TAL.TyVar delta)) `TAL.Seq`
          is1))

toInstrsTAL vm delta gamma (A.Halt ty av) = do
  (sv,_)  <- toSmallVal vm av
  ty' <- toTyTAL ty
  return (Map.empty,
          TAL.Mov TAL.reg1 sv `TAL.Seq`
          TAL.Halt ty')


toDeclTAL :: Varmap -> TAL.Delta -> TAL.Gamma -> A.Decl -> M (Varmap, TAL.Delta, TAL.Gamma, [TAL.Instruction])
toDeclTAL vm delta gamma (A.DeclVar x (Embed av)) = do
  (sv, ty) <- toSmallVal vm av
  (rd, vm') <- var2reg x
  return (Map.union vm vm',
            delta,
            TAL.insertGamma rd ty gamma,
            [TAL.Mov rd sv])

toDeclTAL vm delta gamma (A.DeclPrj i x (Embed av)) = do
  (rd, vm') <- var2reg x
  (sv, ty) <- toSmallVal vm av
  ty1 <- case ty of
        TAL.TyProd tyfs -> do
          when (i >= length tyfs) $ throwError "Ld: index out of range"
          return $ fst (tyfs !! i)
        _ -> throwError "BUG: A.DeclPrj, not a product"
  return (Map.union vm vm',
            delta,
            TAL.insertGamma rd ty1 gamma,
            [TAL.Mov rd sv,
             TAL.Ld rd rd i])

toDeclTAL vm delta gamma (A.DeclPrim x (Embed (av1,p,av2))) = do
  (rd, vm') <- var2reg x
  (sv1, ty1) <- toSmallVal vm av1
  (sv2, ty2) <- toSmallVal vm av2
  let arith = case p of
                   Plus -> TAL.Add
                   Times -> TAL.Mul
                   Minus -> TAL.Sub
  return (Map.union vm vm',
            delta,
            TAL.insertGamma rd TAL.TyInt gamma,
            [TAL.Mov rd sv1, arith rd rd sv2])


toDeclTAL vm delta gamma (A.DeclUnpack a x (Embed av)) = do
  (rd, vm') <- var2reg x
  (sv, ty1) <- toSmallVal vm av
  let a' = translate a
  ty2 <- case ty1 of
              TAL.Exists bnd -> return $ patUnbind a' bnd
              _ -> throwError "BUG: Unpack, not an exists"
  return (Map.union vm vm',
            a' : delta,
            TAL.insertGamma rd ty2 gamma,
            [TAL.Unpack a' rd sv])

toDeclTAL vm delta gamma (A.DeclMalloc x (Embed tys)) = do
  (rd, vm') <- var2reg x
  tys' <- mapM toTyTAL tys
  return (Map.union vm vm',
            delta,
            TAL.insertGamma rd (TAL.TyProd (map (,TAL.Un) tys')) gamma,
            [TAL.Malloc rd tys'])

toDeclTAL vm delta gamma (A.DeclAssign x (Embed (av1, i, av2))) = do
  (rd, vm') <- var2reg x
  (sv1, ty1) <- toSmallVal vm av1
  (sv2, ty2) <- toSmallVal vm av2
  ty <- case ty1 of
        TAL.TyProd tyfs -> do
          when (i >= length tyfs) $ throwError "St: index out of range"
          let (before, _:after) = List.splitAt i tyfs
          return $ TAL.TyProd (before ++ [(ty2,TAL.Init)] ++ after)
        _ -> throwError "BUG: St: not a product"
  return (Map.union vm vm',
            delta,
            TAL.insertGamma rd ty gamma,
            [TAL.Mov rd sv1,
             TAL.Mov (TAL.rtmp 0) sv2,
             TAL.St rd i (TAL.rtmp 0)])

toHeapVal :: Varmap -> A.Ann A.HeapVal -> M (TAL.Heap, TAL.HeapVal)
toHeapVal vm (A.Ann (A.Code bnd)  (A.All bnd')) = do
  mb  <- unbind2 bnd bnd' -- may fail
  case mb of
    Just (as, bnd2, _, tys) -> do
      (xs, e) <- unbind bnd2
      tys' <- mapM toTyTAL tys
      let rs = [TAL.reg1 ..]
      let gamma = zip rs tys'
      let vm' = Map.union vm (Map.fromList (zip xs (map TAL.RegVal rs)))
      let as' = map translate as
      (h, is) <- toInstrsTAL vm' as' gamma e
      return (h, TAL.Code as' gamma is)
    Nothing -> throwError "BUG!"

toHeapVal vm (A.Ann (A.Tuple avs) (A.TyProd tyfs)) = do
  wvs <- mapM (toWordVal vm) avs
  return (Map.empty, TAL.Tuple wvs)

toHeapVal vm _  = throwError "wrong type for heap val"


toProgTAL ::  (A.Tm, A.Heap) -> M TAL.Machine
toProgTAL (tm, A.Heap hp) = do
  let vars   = Map.keys hp
  let labels = map (TAL.Label . translate) vars
  let vm     =
        Map.fromList (zip vars (map (TAL.WordVal . TAL.LabelVal) labels))
  hhvs <- mapM (toHeapVal vm) (Map.elems hp)
  let (heaps, hvals) = unzip hhvs
  let hroot  = Map.fromList (zip labels hvals)
  (hexp, is) <- toInstrsTAL vm [] [] tm
  let heap = Map.unions (hroot : heaps ++ [hexp])
  return (heap, Map.empty, is)
