module F where

import Unbound.Generics.LocallyNameless hiding (prec,empty,Data,Refl)

import Control.Monad
import Control.Monad.Trans.Except
import qualified Data.List as List

import Util
import qualified Text.PrettyPrint as PP

------------------------------------------------------
-- System F with type and term variables
------------------------------------------------------

type TyName = Name Ty
type TmName = Name Tm

data Ty = TyVar TyName
        | TyInt
        | Arr Ty Ty
        | All (Bind TyName Ty)
        | TyProd [Ty]
   deriving (Show, Generic)

data Tm = TmInt Int
        | TmVar TmName
        | Fix (Bind (TmName, TmName, Embed (Ty, Ty)) Tm)
        | App Tm Tm
        | TmProd [Tm]
        | TmPrj Tm Int
        | TmPrim Tm Prim Tm 
        | TmIf0 Tm Tm Tm
        | TLam (Bind TyName Tm)
        | TApp Tm Ty
        | Ann Tm Ty
   deriving (Show, Generic)



------------------------------------------------------
instance Alpha Ty 
instance Alpha Tm 

instance Subst Tm Prim  
instance Subst Tm Ty
instance Subst Ty Prim
instance Subst Ty Tm
instance Subst Tm Tm where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing
  
------------------------------------------------------
-- Example terms
------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
f :: Name Tm
n :: Name Tm
(x,y,z,f,n) = (string2Name "x", string2Name "y", string2Name "z", string2Name "f", string2Name "n")

a :: Name Ty
b :: Name Ty
c :: Name Ty
(a,b,c) = (string2Name "a", string2Name "b", string2Name "c")

-- /\a. \x:a. x
polyid :: Tm
polyid = TLam (bind a (Fix (bind (y, x, Embed (TyVar a, TyVar a)) (TmVar x))))


-- /\a. \x:a. x
polyconst :: Tm
polyconst = TLam (bind a (Fix (bind (y, x, Embed (TyVar a, TyInt)) (TmInt 3))))


-- All a. a -> a
polyidty :: Ty
polyidty = All (bind a (Arr (TyVar a) (TyVar a)))


two :: Tm
two = App (Fix (bind (y, x, Embed (TyInt, TyInt))
                (TmPrim (TmVar x) Plus (TmInt 1)))) (TmInt 1)

-- 1 + 1
onePlusOne :: Tm 
onePlusOne = TmPrim (TmInt 1) Plus (TmInt 1)

-- Factorial function applied to 6
sixfact :: Tm
sixfact = App (Fix (bind (f, n, Embed (TyInt, TyInt))
                    (TmIf0 (TmVar n) (TmInt 1) 
                     (TmPrim (TmVar n) Times
                      (App (TmVar f) 
                       (TmPrim (TmVar n) Minus (TmInt 1))))))) (TmInt 6)



-- /\a. \f:a. \x:a. f
ctrue :: Tm
ctrue = TLam (bind a 
              (Fix (bind (y,n, Embed (TyVar a, Arr (TyVar a) (TyVar a)))
                    (Fix (bind (z, x, Embed (TyVar a, TyVar a))
                          (TmVar n))))))


-- /\a. \f:a -> a. \x:a. f (f x)
twice = TLam (bind a 
              (Fix (bind (y,f, Embed (Arr (TyVar a) (TyVar a), 
                                      Arr (TyVar a) (TyVar a)))
                    (Fix (bind (z, x, Embed (TyVar a, TyVar a))
                          (App (TmVar f) (App (TmVar f) (TmVar x))))))))
                           

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Delta = [ TyName ]
type Gamma = [ (TmName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    if v `List.elem` getDelta g then
      return ()
    else
      throwE "NotFound"

lookupTmVar :: Ctx -> TmName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwE "NotFound"

extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : getDelta ctx }

extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : getGamma ctx }

-- could be replaced with fv
tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar x) =
   checkTyVar g x
tcty g  (All b) = do
   (x, ty') <- unbind b
   tcty (extendTy x g) ty'
tcty g  (Arr ty1 ty2) = do
   tcty g  ty1
   tcty g  ty2
tcty g TyInt =  return ()
tcty g (TyProd tys) =
   mapM_ (tcty g) tys
   

typecheck :: Ctx -> Tm -> M Tm
typecheck g e@(TmVar x) = do 
  ty <- lookupTmVar g x
  return $ Ann e ty
typecheck g (Fix bnd) = do
  ((f, x, Embed (ty1, ty2)), e1) <- unbind bnd
  tcty g ty1
  tcty g ty2
  ae1 <- typecheck (extendTm f (Arr ty1 ty2) (extendTm x ty1 g)) e1
  case ae1 of 
    (Ann _ ty2') ->
      if not (ty2 `aeq` ty2')
      then throwE $ "Type Error: Can't match " ++ pp ty2 ++ " and " ++ pp ty2'
      else return $ Ann 
           (Fix (bind (f,x, Embed (ty1, ty2)) ae1))
           (Arr ty1 ty2)
    _ -> throwE "Annotated expression expected"
typecheck g e@(App e1 e2) = do
  ae1 <- typecheck g e1
  ae2 <- typecheck g e2
  case (ae1, ae2) of 
    (Ann _ ty1, Ann _ ty2) ->
      case ty1 of
        Arr ty11 ty21 | ty2 `aeq` ty11 ->
          return (Ann (App ae1 ae2) ty21)
        _ -> throwE "TypeError"
typecheck g (TLam bnd) = do
  (x, e) <- unbind bnd
  ae <- typecheck (extendTy x g) e
  case ae of 
    (Ann _ ty) -> 
      return $ Ann (TLam (bind x ae)) (All (bind x ty))
typecheck g (TApp e ty) = do
  ae <- typecheck g e
  case ae of 
    (Ann _ tyt) -> 
      case tyt of
        (All b) -> do
            tcty g ty
            (n1, ty1) <- unbind b
            return $ Ann (TApp ae ty) (subst n1 ty ty1)
        _ -> throwE "TypeError"
typecheck g (TmProd es) = do 
  atys <- mapM (typecheck g) es
  let tys = map (\(Ann _ ty) -> ty) atys
  return $ Ann (TmProd atys) (TyProd tys)
typecheck g (TmPrj e i) = do
  ae <- typecheck g e
  case ae of 
    (Ann _ ty) -> 
      case ty of 
        TyProd tys | i < length tys -> return $ Ann (TmPrj ae i) (tys !! i)
        _ -> throwE "TypeError"
typecheck g (TmInt i) = return (Ann (TmInt i) TyInt)
typecheck g (TmPrim e1 p e2) = do
  ae1 <- typecheck g e1
  ae2 <- typecheck g e2
  case (ae1, ae2) of 
    (Ann _ ty1, Ann _ ty2) ->      
      case (ty1 , ty2) of 
        (TyInt, TyInt) -> return (Ann (TmPrim ae1 p ae2) TyInt)
        _ -> throwE "TypeError"
typecheck g (TmIf0 e0 e1 e2) = do
  ae0 <- typecheck g e0
  ae1 <- typecheck g e1
  ae2 <- typecheck g e2
  case (ae0, ae1, ae2) of 
    (Ann _ ty0, Ann _ ty1, Ann _ ty2) ->
      if ty1 `aeq` ty2 && ty0 `aeq` TyInt then 
        return (Ann (TmIf0 ae0 ae1 ae2) ty1)
      else   
        throwE "TypeError"
typecheck g _ = throwE "TypeError"
-----------------------------------------------------------------
-- Small-step semantics
-----------------------------------------------------------------

value :: Tm -> Bool
value (TmInt _)  = True
value (Fix _)    = True
value (TmProd es) = all value es
value (TLam _)   = True
value _          = False

steps :: [Tm] -> M [Tm]
steps [] = throwE "can't step empty list"
steps (e:es) | value e = do
  es' <- steps es
  return (e : es')
steps (e:es) = do 
  e'  <- step e
  return (e' : es)
  
step :: Tm -> M Tm
step e | value e = throwE "can't step value"
step (TmVar _)   = throwE "unbound variable" 
step (App e1@(Fix bnd) e2) = 
  if value e2 
  then do
    ((f, x, _), t) <- unbind bnd
    return $ substs [ (x, e2), (f,e1) ] t
  else do          
    e2' <- step e2
    return (App e1 e2') 
step (App e1 e2) = do
  e1' <- step e1
  return (App e1' e2)
step (TmPrj e1@(TmProd es) i) | value e1 && i < length es = return $ es !! i
step (TmPrj e1 i) = do 
  e1' <- step e1
  return (TmPrj e1' i) 
step (TmProd es) = do
  es' <- steps es
  return (TmProd es')
step (TmPrim (TmInt i1) p (TmInt i2)) = 
  return (TmInt (evalPrim p i1 i2))
step (TmPrim e1 p e2) | value e1 = do
  e2' <- step e2
  return (TmPrim e1 p e2')
  | otherwise = do
  e1' <- step e1
  return (TmPrim e1' p e2)
step (TmIf0 (TmInt i) e1 e2) = if i==0 then return e1 else return e2
step (TmIf0 e0 e1 e2) = do 
  e0' <- step e0
  return (TmIf0 e0' e1 e2)
step (TApp (TLam bnd) ty) = do
  (a, e) <- unbind bnd
  return $ subst a ty e
step (TApp e ty) = do
  e' <- step e 
  return $ TApp e' ty
step (Ann e ty) = return e
  
evaluate :: Tm -> M Tm
evaluate e = if value e then return e else do
  e' <- step e
  evaluate e'
  
-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display (TyVar n)     = display n
  display TyInt       = return $ text "Int"
  display (Arr ty1 ty2) = do  
    d1 <- withPrec (precedence "->" + 1) $ display ty1
    d2 <- withPrec (precedence "->")     $ display ty2
    binop d1 "->" d2
  display (All bnd) = lunbind bnd $ \ (a,ty) -> do
    da <- display a
    dt <- display ty
    prefix "forall" (da PP.<> text "." <+> dt)
  display (TyProd tys) = displayTuple tys
    
instance Display Tm where
  display (TmInt i) = return $ int i
  display (TmVar n) = display n
  display (Fix bnd) = lunbind bnd $ \((f,x,Embed (ty1,ty2)), e) -> do
    df <- display f 
    dx <- display x      
    d1 <- display ty1      
    d2 <- display ty2
    de <- withPrec (precedence "fix") $ display e
    let arg = parens (dx PP.<> colon PP.<> d1)
    --if f `elem` (fv e :: [F.TmName])
      -- then 
    prefix "fix" (df <+> arg PP.<> colon PP.<> d2 PP.<> text "." <+> de)
      -- else prefix "\\"  (arg PP.<> text "." <+> de)
  display (App e1 e2) = do
    d1 <- withPrec (precedence " ") $ display e1
    d2 <- withPrec (precedence " " + 1) $ display e2
    binop d1 " " d2
  display (TmProd es) = displayTuple es

  display (TmPrj e i) = do
    de <- display e 
    return $ text "Pi" PP.<> int i <+> de
  display (TmPrim e1 p e2) = do 
    let str = show p
    d1 <- withPrec (precedence str)     $ display e1 
    d2 <- withPrec (precedence str + 1) $ display e2 
    binop d1 str d2
  display (TmIf0 e0 e1 e2) = do
    d0 <- display e0
    d1 <- display e1
    d2 <- display e2
    prefix "if0" $ sep [d0 , text "then" <+> d1 , text "else" <+> d2]
  display (TLam bnd) = lunbind bnd $ \(a,e) -> do
    da <- display a
    de <- withPrec (precedence "/\\") $ display e
    prefix "/\\" (da PP.<> text "." <+> de)
  display (TApp e ty) = do
    d1 <- withPrec (precedence " ") $ display e
    d2 <- withPrec (precedence " " + 1) $ display ty
    binop d1 " " d2
  display (Ann e ty) = display e