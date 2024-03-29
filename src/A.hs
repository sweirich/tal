module A where
  
import GHC.Generics
import Unbound.Generics.LocallyNameless hiding (prec,empty,Data,Refl,Val)
import Unbound.Generics.LocallyNameless.Alpha

import Control.Monad
import Control.Monad.Except

import Data.Monoid (Monoid(..))

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map


import Util
import Text.PrettyPrint as PP


-- System A

type TyName = Name Ty
type ValName = Name Val

data Flag = Un | Init
  deriving (Eq, Ord, Show, Generic)

data Ty = TyVar TyName
        | TyInt
        | All (Bind [TyName] [Ty])
        | TyProd [(Ty, Flag)]  -- new
        | Exists (Bind TyName Ty) 
   deriving (Show, Generic)

data Val = TmInt Int
        | TmVar ValName
        | TApp (Ann Val) Ty  
        | Pack Ty (Ann Val)  
   deriving (Show, Generic)       
            
data Ann v = Ann v Ty
   deriving (Show, Generic)
            
data Decl   = 
    DeclVar     ValName (Embed (Ann Val))
  | DeclPrj     Int ValName (Embed (Ann Val))
  | DeclPrim    ValName (Embed (Ann Val, Prim, Ann Val))
  | DeclUnpack  TyName ValName (Embed (Ann Val))  
  | DeclMalloc  ValName (Embed [Ty]) -- new
  | DeclAssign  ValName (Embed (Ann Val, Int, Ann Val)) --new
     -- x = v1 [i] <- v2
    deriving (Show, Generic)
             
data Tm = 
    Let   (Bind Decl Tm)
  | App   (Ann Val) [Ann Val] 
  | TmIf0 (Ann Val) Tm Tm
  | Halt  Ty (Ann Val)    
    deriving (Show, Generic)

data HeapVal = 
    Tuple [Ann Val]
  | Code (Bind [TyName] (Bind [ValName] Tm))
    deriving (Show, Generic)

newtype Heap = Heap (Map ValName (Ann HeapVal)) 
  deriving (Semigroup, Monoid)

------------------------------------------------------
instance Alpha Flag
instance Alpha Ty 
instance Alpha Val 
instance Alpha a => Alpha (Ann a)
instance Alpha Decl
instance Alpha Tm

instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Ty Prim
instance Subst Ty Tm
instance Subst Ty (Ann Val)
instance Subst Ty Decl
instance Subst Ty Val
instance Subst Ty Flag

instance Subst Val Flag
instance Subst Val Prim
instance Subst Val Ty
instance Subst Val (Ann Val)
instance Subst Val Decl
instance Subst Val Tm
instance Subst Val Val where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
  
------------------------------------------------------
-- Helper functions
------------------------------------------------------

-- Tag all error messages as from this module
throwErrorA :: MonadError String m => String -> m a
throwErrorA s = throwError ("A:" ++ s)

mkTyApp :: (MonadError String m, Fresh m) => Ann Val -> [Ty] -> m (Ann Val)
mkTyApp av [] = return av
mkTyApp av@(Ann _ (All bnd)) (ty:tys) = do
    (as, atys) <- unbind bnd               
    case as of 
      a:as' -> 
        let atys' = subst a ty atys in
        mkTyApp (Ann (TApp av ty) (All (bind as' atys'))) tys
      _ -> throwErrorA "mkTyApp: not a polymorphic All"
mkTyApp (Ann _ ty) _ = throwErrorA "type error: not an All"

lets :: [Decl] -> Tm -> Tm
lets [] tm = tm 
lets (d:ds) tm = Let (bind d (lets ds tm))

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------

type Delta = [ TyName ]
type Gamma = [ (ValName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
  deriving Show
  
emptyCtx :: Ctx
emptyCtx = Ctx { getDelta = [], getGamma = [] }

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    unless (v `List.elem` getDelta g) $ 
      throwErrorA $ "Type variable not found " ++ show v ++ "\n"
            ++ "in context: " ++ pp g

lookupTmVar :: Ctx -> ValName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwErrorA $ "Term variable not found " ++ show v ++ "\n"
        ++ "in context: " ++ pp g

extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : getDelta ctx }

extendTys :: [TyName] -> Ctx -> Ctx
extendTys ns ctx = foldr extendTy ctx ns

extendTm :: ValName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : getGamma ctx }

extendTms :: [ValName] -> [Ty] -> Ctx -> Ctx
extendTms [] [] ctx = ctx
extendTms (n:ns) (ty:tys) ctx = extendTm n ty (extendTms ns tys ctx)
extendTms _ _ _ = error "wrong number"


tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar x) =
   checkTyVar g x
tcty g  (All b) = do
   (xs, tys) <- unbind b
   let g' = extendTys xs g
   mapM_ (tcty g') tys
tcty g TyInt =  return ()
tcty g (TyProd tys) = do
   mapM_ (tcty g . fst) tys
tcty g (Exists b) = do 
  (a, ty) <- unbind b
  tcty (extendTy a g) ty


typecheckHeapVal :: Ctx -> Ann HeapVal -> M Ty
typecheckHeapVal g (Ann (Code bnd) (All bnd')) = do  
  mb  <- unbind2 bnd bnd' -- may fail
  case mb of 
    Just (as, bnd2, _, tys) -> do
      (xs, e) <- unbind bnd2
      let g' = extendTys as g
      mapM_ (tcty g') tys
      typecheck (extendTms xs tys g') e
      return (All bnd')
    Nothing -> throwErrorA "wrong # of type variables"
typecheckHeapVal g (Ann (Code bnd) _ ) = 
    throwErrorA "code must have forall type"
  
typecheckHeapVal g (Ann (Tuple es) ty) = do 
  tys <- mapM (typecheckAnnVal g) es
  let ty' = TyProd $ map (,Un) tys 
  if ty `aeq` ty' 
    then return ty
    else throwErrorA "incorrect annotation on tuple"

typecheckVal :: Ctx -> Val -> M Ty
typecheckVal g (TmVar x) = lookupTmVar g x
typecheckVal g (TmInt i)    = return TyInt
typecheckVal g (TApp av ty) = do
  tcty g ty
  ty' <- typecheckAnnVal g av
  case ty' of 
    All bnd -> do 
      (as, bs) <- unbind bnd
      case as of 
        [] -> throwErrorA "can't instantiate non-polymorphic function"
        (a:as') -> do
          let bs' = subst a ty bs
          return (All (bind as' bs'))
    _ -> throwErrorA "type error"
typecheckVal g (Pack _ _) = throwErrorA "pack must be annotated"

typecheckAnnVal :: Ctx -> Ann Val -> M Ty
typecheckAnnVal g (Ann (Pack ty1 av) ty) = do
  case ty of 
    Exists bnd -> do 
      (a, ty2) <- unbind bnd
      tcty g ty1
      ty' <- typecheckAnnVal g av
      if not (ty' `aeq` subst a ty1 ty2)
         then throwErrorA "type error"
         else return ty 
    _ -> throwErrorA "must be exists for pack"    
typecheckAnnVal g (Ann v ty) = do  
  tcty g ty
  ty' <- typecheckVal g v 
  if ty `aeq` ty'
     then return ty
     else throwErrorA $ "wrong annotation on: " ++ pp v ++ "\nInferred: " ++ pp ty' ++ "\nAnnotated: " ++ pp ty 

typecheckDecl :: Ctx -> Decl -> M Ctx
typecheckDecl g (DeclVar x (Embed av)) = do
  ty <- typecheckAnnVal g av
  return $ extendTm x ty g
typecheckDecl g (DeclPrj i x (Embed av@(Ann v _))) = do
  ty <- typecheckAnnVal g av
  case ty of 
    TyProd tys | i < length tys -> 
      return $ extendTm x (fst (tys !! i)) g
    _ -> throwErrorA "cannot project"
typecheckDecl g (DeclPrim x (Embed (av1, _, av2))) = do
  ty1 <- typecheckAnnVal g av1
  ty2 <- typecheckAnnVal g av2
  case (ty1 , ty2) of 
    (TyInt, TyInt) -> return $ extendTm x TyInt g
    _ -> throwErrorA "TypeError"
typecheckDecl g (DeclUnpack a x (Embed av)) = do
  tya <- typecheckAnnVal g av
  case tya of 
    Exists bnd -> do 
      let ty = patUnbind a bnd 
      return $ extendTy a (extendTm x ty g)
    _ -> throwErrorA "TypeError"
typecheckDecl g (DeclMalloc x (Embed tys)) = do                
  mapM_ (tcty g) tys
  return $ extendTm x (TyProd (map (,Un) tys)) g      
typecheckDecl g (DeclAssign x (Embed (av1@(Ann v1 _), i, av2))) = do
  ty1 <- typecheckAnnVal g av1 
  ty2 <- typecheckAnnVal g av2
  case ty1 of 
    TyProd tys | i < length tys -> 
      let (xs,(ty,_):ys) = splitAt i tys in
      if ty `aeq` ty2 
        then return $ extendTm x (TyProd (xs ++ (ty,Init) : ys)) g
        else throwErrorA "TypeError"
    _ -> throwErrorA "TypeError"
         
typecheck :: Ctx -> Tm -> M ()
typecheck g (Let bnd) = do
  (d,e) <- unbind bnd
  g' <- typecheckDecl g d
  typecheck g' e
typecheck g (App av es) = do
  ty <- typecheckAnnVal g av
  case ty of
   (All bnd) -> do
     (as, argtys) <- unbind bnd
     argtys' <- mapM (typecheckAnnVal g) es
     if not (null as)  
       then throwErrorA "must use type application"
       else 
         if length argtys /= length argtys'
           then throwErrorA "incorrect args"
           else unless (and (zipWith aeq argtys argtys')) $ 
              throwErrorA "arg mismatch"
   _ -> throwErrorA "need forall type"
typecheck g (TmIf0 av e1 e2) = do
  ty0 <- typecheckAnnVal g av
  typecheck g e1
  typecheck g e2
  if ty0 `aeq` TyInt then 
    return ()
  else   
    throwErrorA "TypeError"
typecheck g (Halt ty av) = do
  ty' <- typecheckAnnVal g av
  unless (ty `aeq` ty') $
    throwErrorA "type error"

         
         
progcheck :: (Tm, Heap) -> M ()
progcheck (tm, Heap m) = do
  let g = 
        Map.foldlWithKey (\ctx x (Ann _ ty) -> extendTm x ty ctx) 
        emptyCtx m
  mapM_ (typecheckHeapVal g) (Map.elems m)
  typecheck g tm

-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display (TyVar n)     = display n
  display TyInt       = return $ text "Int"
  display (All bnd) = lunbind bnd $ \ (as,tys) -> do
    da <- displayList as
    dt <- displayList tys
    if null as 
      then return $ parens dt <+> text "-> void"
      else prefix "forall" (brackets da PP.<> text "." <+> parens dt <+> text "-> void")
  display (TyProd tys) = displayTuple tys
  display (Exists bnd) = lunbind bnd $ \ (a,ty) -> do
    da <- display a 
    dt <- display ty
    prefix "exists" (da PP.<> text "." <+> dt)
    
instance Display (Ty, Flag) where    
  display (ty, fl) = do
    dty <- display ty
    let f = case fl of { Un -> "0" ; Init -> "1" }
    return $ dty PP.<> text "^" PP.<> text f
    
instance Display (ValName,Embed Ty) where                         
  display (n, Embed ty) = do
    dn <- display n
    dt <- display ty
    return $ dn PP.<> colon PP.<> dt
    
instance Display Val where                         
  display (TmInt i) = return $ int i
  display (TmVar n) = display n
  display (Pack ty e) = do 
    dty <- display ty
    de  <- display e 
    prefix "pack" (brackets (dty PP.<> comma PP.<> de))
  display (TApp av ty) = do
    dv <- display av
    dt <- display ty
    return $ dv <+> brackets dt

instance Display HeapVal where
  display (Code bnd) = lunbind bnd $ \(as, bnd2) -> lunbind bnd2 $ \(xtys, e) -> do
    ds    <- displayList as  
    dargs <- displayList xtys
    de    <- withPrec (precedence "code") $ display e
    let tyArgs = if null as then empty else brackets ds
    let tmArgs = if null xtys then empty else parens dargs
    prefix "code"  (tyArgs PP.<> tmArgs PP.<> text "." $$ de)
    
  display (Tuple es) = displayTuple es
  

instance Display a => Display (Ann a) where
  display (Ann av _) = display av

instance Display Tm where
  display (App av args) = do
    da    <- display av
    dargs <- displayList args
    let tmArgs = if null args then empty else space PP.<> parens dargs
    return $ da PP.<> tmArgs
  display (Halt ty v) = do 
    dv <- display v
    --dt <- display ty
    return $ text "halt" <+> dv -- <+> text ":" <+> dt
  display (Let bnd) = lunbind bnd $ \(d, e) -> do
    dd <- display d
    de <- display e
    return (text "let" <+> dd <+> text "in" $$ de)
  display (TmIf0 e0 e1 e2) = do
    d0 <- display e0
    d1 <- display e1
    d2 <- display e2
    prefix "if0" $ parens $ sep [d0 PP.<> comma , d1 PP.<> comma, d2]

instance Display Decl where
  display (DeclVar x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> dv
  display (DeclPrj i x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> text "pi" PP.<> int i <+> dv
  display (DeclPrim x (Embed (e1, p, e2))) = do
    dx <- display x
    let str = show p
    d1 <- display e1 
    d2 <- display e2 
    return $ dx <+> text "=" <+> d1 <+> text str <+> d2
  display (DeclUnpack a x (Embed av)) = do
    da <- display a
    dx <- display x
    dav <- display av
    return $ brackets (da PP.<> comma PP.<> dx) <+> text "=" <+> dav
  display (DeclMalloc x (Embed tys)) = do
    dx <- display x
    dtys <- displayTuple tys
    return $ dx <+> text "= malloc" PP.<> dtys
  display (DeclAssign x (Embed (av1, i, av2))) = do
    dx <- display x
    dav1 <- display av1
    dav2 <- display av2
    return $ dx <+> text "=" <+> dav1 <+> brackets (text (show i)) 
      <+>  text "<-" <+> dav2

instance Display Heap where
  display (Heap m) = do
    fcns <- mapM (\(d,v) -> do 
                     dn <- display d
                     dv <- display v
                     return (dn, dv)) (Map.toList m)
    return $ hang (text "letrec") 2 $ 
      vcat [ n <+> text "=" <+> dv | (n,dv) <- fcns ]

instance Display (Tm, Heap) where
  display (tm,h) = do
    dh <- display h
    dt <- display tm
    return $ dh $$ text "in" <+> dt

instance Display (ValName, Ty) where
  display (v, ty) = do
    dt <- display ty
    return $ text (show v) <+> colon <+> dt

instance Display Ctx where
  display (Ctx delta gamma) = do
    tyvars <- mapM display delta
    tmvars <- mapM display gamma
    return $ vcat [text "delta:" <+> hsep tyvars,
                   text "gamma:" <+> sep tmvars ]