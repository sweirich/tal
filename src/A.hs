{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             TupleSections,
             GADTs #-}

module A where

import Unbound.LocallyNameless hiding (prec,empty,Data,Refl,Val)

import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Types

import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map


import Util
import Text.PrettyPrint as PP


------------------
-- should move to Unbound.LocallyNameless.Ops
patUnbind :: (Alpha p, Alpha t) => p -> Bind p t -> t
patUnbind p (B _ t) = openT p t
------------------


-- System A

type TyName = Name Ty
type ValName = Name Val

data Flag = Un | Init
  deriving (Eq, Ord, Show)

data Ty = TyVar TyName
        | TyInt
        | All (Bind [TyName] [Ty])
        | TyProd [(Ty, Flag)]  -- new
        | Exists (Bind TyName Ty) 
   deriving Show

data Val = TmInt Int
        | TmVar ValName
        | TApp (Ann Val) Ty  
        | Pack Ty (Ann Val)  
   deriving Show       
            
data Ann v = Ann v Ty
   deriving Show
            
data Decl   = 
    DeclVar     ValName (Embed (Ann Val))
  | DeclPrj Int ValName (Embed (Ann Val))
  | DeclPrim    ValName (Embed ((Ann Val), Prim, (Ann Val)))
  | DeclUnpack  TyName ValName (Embed (Ann Val))  
  | DeclMalloc  ValName (Embed [Ty]) -- new
  | DeclAssign  ValName (Embed ((Ann Val), Int, (Ann Val))) --new
     -- x = v1 [i] <- v2
    deriving Show
             
data Tm = 
    Let (Bind Decl Tm)
  | App   (Ann Val) [(Ann Val)] 
  | TmIf0 (Ann Val) Tm Tm
  | Halt  Ty (Ann Val)    
    deriving Show

data HeapVal = 
    Tuple [(Ann Val)]
  | Code (Bind [TyName] (Bind [ValName] Tm))
    deriving Show

newtype Heap = Heap (Map ValName (Ann HeapVal)) deriving Show

instance Monoid A.Heap where
  mempty  = A.Heap Map.empty
  mappend (A.Heap h1) (A.Heap h2) = A.Heap (Map.union h1 h2)

$(derive [''HeapVal, ''Flag, ''Ty, ''Val, ''Ann, ''Decl, ''Tm])

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

mkTyApp :: (MonadError String m, Fresh m) => (Ann Val) -> [Ty] -> m (Ann Val)
mkTyApp av [] = return av
mkTyApp av@(Ann _ (All bnd)) (ty:tys) = do
    (as, atys) <- unbind bnd               
    case as of 
      a:as' -> 
        let atys' = subst a ty atys in
        mkTyApp (Ann (TApp av ty) (All (bind as' atys'))) tys
      _ -> throwError "type error: not a polymorphic All"
mkTyApp (Ann _ ty) _ = throwError "type error: not an All"

lets :: [Decl] -> Tm -> Tm
lets [] tm = tm 
lets (d:ds) tm = Let (bind d (lets ds tm))

-----------------------------------------------------------------
-- Free variables, with types
-----------------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
(x,y,z) = (string2Name "x", string2Name "y", string2Name "z")

a :: Name Ty
b :: Name Ty
c :: Name Ty
(a,b,c) = (string2Name "a", string2Name "b", string2Name "c")

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------

type Delta = [ TyName ]
type Gamma = [ (ValName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    if List.elem v (getDelta g) then
      return ()
    else
      throwError $ "Type variable not found " ++ (show v)

lookupTmVar :: Ctx -> ValName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError $ "Term variable notFound " ++ (show v)

extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : (getDelta ctx) }

extendTys :: [TyName] -> Ctx -> Ctx
extendTys ns ctx = foldr extendTy ctx ns

extendTm :: ValName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

extendTms :: [ValName] -> [Ty] -> Ctx -> Ctx
extendTms [] [] ctx = ctx
extendTms (n:ns) (ty:tys) ctx = extendTm n ty (extendTms ns tys ctx)

{-
extendDecl :: Decl -> Ctx -> Ctx
extendDecl (DeclVar x (Embed (Ann _ ty))) = extendTm x ty
extendDecl (DeclPrj i x (Embed (Ann _ (TyProd tys)))) = extendTm x (tys !! i)                                           
extendDecl (DeclPrim x  _) = extendTm x TyInt
extendDecl (DeclUnpack b x (Embed (Ann _ (Exists bnd)))) = 
  extendTy b . extendTm x (patUnbind b bnd)
-}


tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar x) =
   checkTyVar g x
tcty g  (All b) = do
   (xs, tys) <- unbind b
   let g' = extendTys xs g -- XX
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
    Nothing -> throwError "wrong # of type variables"
  
typecheckHeapVal g (Ann (Tuple es) ty) = do 
  tys <- mapM (typecheckAnnVal g) es
  let ty' = TyProd $ map (,Un) tys 
  if ty `aeq` ty' 
    then return ty
    else throwError "incorrect annotation on tuple"

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
        [] -> throwError "can't instantiate non-polymorphic function"
        (a:as') -> do
          let bs' = subst a ty bs
          return (All (bind as' bs'))

typecheckAnnVal g (Ann (Pack ty1 av) ty) = do
  case ty of 
    Exists bnd -> do 
      (a, ty2) <- unbind bnd
      tcty g ty1
      ty' <- typecheckAnnVal g av
      if (not (ty' `aeq` subst a ty1 ty2)) 
         then throwError "type error"
         else return ty     
typecheckAnnVal g (Ann v ty) = do  
  tcty g ty
  ty' <- typecheckVal g v 
  if (ty `aeq` ty') 
     then return ty
     else throwError $ "wrong annotation on: " ++ pp v ++ "\nInferred: " ++ pp ty ++ "\nAnnotated: " ++ pp ty' 

typecheckDecl g (DeclVar x (Embed av)) = do
  ty <- typecheckAnnVal g av
  return $ extendTm x ty g
typecheckDecl g (DeclPrj i x (Embed av)) = do
  ty <- typecheckAnnVal g av
  case ty of 
    TyProd tys | i < length tys -> 
      return $ extendTm x (fst (tys !! i)) g
    _ -> throwError "cannot project"
typecheckDecl g (DeclPrim x (Embed (av1, _, av2))) = do
  ty1 <- typecheckAnnVal g av1
  ty2 <- typecheckAnnVal g av2
  case (ty1 , ty2) of 
    (TyInt, TyInt) -> return $ extendTm x TyInt g
    _ -> throwError "TypeError"
typecheckDecl g (DeclUnpack a x (Embed av)) = do
  tya <- typecheckAnnVal g av
  case tya of 
    Exists bnd -> do 
      let ty = patUnbind a bnd 
      return $ extendTy a (extendTm x ty g)
    _ -> throwError "TypeError"
typecheckDecl g (DeclMalloc x (Embed tys)) = do                
  mapM_ (tcty g) tys
  return $ extendTm x (TyProd (map (,Un) tys)) g      
typecheckDecl g (DeclAssign x (Embed (v1, i, v2))) = do
  ty1 <- typecheckAnnVal g v1 
  ty2 <- typecheckAnnVal g v2
  case ty1 of 
    TyProd tys | i < length tys -> 
      let (xs,(ty,_):ys) = splitAt i tys in
      return $ extendTm x (TyProd (xs ++ (ty,Init) : ys)) g
         
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
     if length as /= 0 
       then throwError "must use type application"
       else 
         if (length argtys /= length argtys') 
           then throwError "incorrect args"
           else if (not (all id (zipWith aeq argtys argtys'))) then 
              throwError "arg mismatch"
              else return ()
typecheck g (TmIf0 av e1 e2) = do
  ty0 <- typecheckAnnVal g av
  typecheck g e1
  typecheck g e2
  if ty0 `aeq` TyInt then 
    return ()
  else   
    throwError "TypeError"
typecheck g (Halt ty av) = do
  ty' <- typecheckAnnVal g av
  if (not (ty `aeq` ty'))
    then throwError "type error"
    else return ()
         
         
progcheck (tm, Heap m) = do
  let g = 
        Map.foldlWithKey (\ctx x (Ann _ ty) -> extendTm x ty ctx) 
        emptyCtx m
  -- mapM_ (heapvalcheck g') (Map.elems m)
  typecheck g tm



-----------------------------------------------------------------
-- Small-step semantics
-----------------------------------------------------------------
  
{-
mkSubst :: Decl -> M (Tm,Heap) -> (Tm,Heap)
mkSubst (DeclVar   x (Embed (Ann v _))) = return $ subst x v
mkSubst (DeclPrj i x (Embed (Ann (TmProd avs) _))) | i < length avs =
       let Ann vi _ = avs !! i in return $ subst x vi
mkSubst (DeclPrim  x (Embed (Ann (TmInt i1) _, p, Ann (TmInt i2) _))) = 
       let v = TmInt (evalPrim p i1 i2) in
       return $ subst x v
mkSubst (DeclUnpack a x (Embed (Ann (Pack ty (Ann u _)) _))) = 
  return $ subst a ty . subst x u  
mkSubst (DeclPrj i x (Embed av)) = 
  throwError $ "invalid prj " ++ pp i ++ ": " ++ pp av
mkSubst (DeclUnpack a x (Embed av)) = 
  throwError $ "invalid unpack:" ++ pp av



step :: (Tm, Heap) -> M (Tm, Heap)

step (Let bnd, heap) = do
  (d, e) <- unbind bnd
  ss     <- mkSubst d
  return $ ss (e, heap)
      
step (App (Ann e1@(Fix bnd) _) avs) = do
    ((f, as), bnd2) <- unbind bnd
    (xtys, e) <- unbind bnd2
    let us = map (\(Ann u _) -> u) avs
    let xs = map fst xtys
    return $ substs ((f,e1):(zip xs us)) e

step (TmIf0 (Ann (TmInt i) _) e1 e2) = if i==0 then return e1 else return e2

step _ = throwError "cannot step"
  
evaluate :: Tm -> M Val
evaluate (Halt _ (Ann v _)) = return v
evaluate e = do
  e' <- step e
  evaluate e'
-}  
-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display (TyVar n)     = display n
  display (TyInt)       = return $ text "Int"
  display (All bnd) = lunbind bnd $ \ (as,tys) -> do
    da <- displayList as
    dt <- displayList tys
    if null as 
      then return $ parens dt <+> text "-> void"
      else prefix "forall" (brackets da <> text "." <+> parens dt <+> text "-> void")
  display (TyProd tys) = displayTuple tys
  display (Exists bnd) = lunbind bnd $ \ (a,ty) -> do
    da <- display a 
    dt <- display ty
    prefix "exists" (da <> text "." <+> dt)
    
instance Display (Ty, Flag) where    
  display (ty, fl) = do
    dty <- display ty
    let f = case fl of { Un -> "0" ; Init -> "1" }
    return $ dty <> text "^" <> text f
    
instance Display (ValName,Embed Ty) where                         
  display (n, Embed ty) = do
    dn <- display n
    dt <- display ty
    return $ dn <> colon <> dt
    
instance Display Val where                         
  display (TmInt i) = return $ int i
  display (TmVar n) = display n
  display (Pack ty e) = do 
    dty <- display ty
    de  <- display e 
    prefix "pack" (brackets (dty <> comma <> de))
  display (TApp av ty) = do
    dv <- display av
    dt <- display ty
    return $ dv <+> (brackets dt)

instance Display HeapVal where
  display (Code bnd) = lunbind bnd $ \(as, bnd2) -> lunbind bnd2 $ \(xtys, e) -> do
    ds    <- displayList as  
    dargs <- displayList xtys
    de    <- withPrec (precedence "code") $ display e
    let tyArgs = if null as then empty else brackets ds
    let tmArgs = if null xtys then empty else parens dargs
    prefix "code"  (tyArgs <> tmArgs <> text "." $$ de)
    
  display (Tuple es) = displayTuple es
  

instance Display a => Display (Ann a) where
{-  display (Ann av ty) = do
    da <- display av
    dt <- display ty
    return $ parens (da <> text ":" <> dt) -}
  display (Ann av _) = display av

instance Display Tm where
  display (App av args) = do
    da    <- display av
    dargs <- displayList args
    let tmArgs = if null args then empty else space <> parens dargs
    return $ da <> tmArgs
  display (Halt ty v) = do 
    dv <- display v
    --dt <- display ty
    return $ text "halt" <+> dv -- <+> text ":" <+> dt
  display (Let bnd) = lunbind bnd $ \(d, e) -> do
    dd <- display d
    de <- display e
    return $ (text "let" <+> dd <+> text "in" $$ de)
  display (TmIf0 e0 e1 e2) = do
    d0 <- display e0
    d1 <- display e1
    d2 <- display e2
    prefix "if0" $ parens $ sep [d0 <> comma , d1 <> comma, d2]

instance Display Decl where
  display (DeclVar x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> dv
  display (DeclPrj i x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> text "pi" <> int i <+> dv
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
    return $ brackets (da <> comma <> dx) <+> text "=" <+> dav
  display (DeclMalloc x (Embed tys)) = do
    dx <- display x
    dtys <- displayTuple tys
    return $ dx <+> text "= malloc" <> dtys
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