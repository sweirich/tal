{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             TupleSections,
             GeneralizedNewtypeDeriving,
             GADTs #-}

module TAL where

import Unbound.LocallyNameless hiding (prec,empty,Data,Refl,Val)

import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Types

import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Reader


import Data.Monoid (Monoid(..))

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map


import Util
import Text.PrettyPrint as PP

-- Typed Assembly Language

type TyName = Name Ty

data Ty = TyVar TyName
        | TyInt
        | All (Bind [TyName] Gamma)
        | TyProd [(Ty, Flag)]  
        | Exists (Bind TyName Ty) 
   deriving Show

data Flag = Un | Init
  deriving (Eq, Ord, Show)

-- Heap types
type Psi   = Map Label Ty  
-- Register file types
type Gamma = Map Register Ty

newtype Register = Register String deriving (Eq, Ord, Show)
newtype Label    = Label  (String,Int) deriving (Eq, Ord, Show)

data TyApp a = TyApp a Ty    deriving Show
data Pack  a = Pack  Ty a Ty deriving Show

data WordVal = LabelVal Label
             | TmInt    Int
             | Junk     Ty  
             | WApp  (TyApp WordVal)
             | WPack (Pack  WordVal)
   deriving Show

data SmallVal = RegVal Register 
              | WordVal WordVal 
              | SApp  (TyApp SmallVal) 
              | SPack (Pack SmallVal)
   deriving Show
            
data HeapVal = 
    Tuple [WordVal]
  | Code  [TyName] Gamma InstrSeq  -- nominal binding
    deriving Show

type Heap         = Map Label    HeapVal
type RegisterFile = Map Register WordVal
            
data Instruction = 
    Add Register Register SmallVal
  | Bnz Register SmallVal
  | Ld  Register Register Int
  | Malloc Register [Ty]
  | Mov Register SmallVal  
  | Mul Register Register SmallVal  
  | St  Register Int Register  
  | Sub Register Register SmallVal  
  | Unpack TyName Register SmallVal  -- binds type variable
    deriving Show
             
data InstrSeq = 
    Seq Instruction InstrSeq  -- annoying to do bind here, skipping
  | Jump SmallVal
  | Halt  Ty 
    deriving Show

--instance Monoid A.Heap where
--  mempty  = A.Heap Map.empty
--  mappend (A.Heap h1) (A.Heap h2) = A.Heap (Map.union h1 h2)

type Machine = (Heap, RegisterFile, InstrSeq)

$(derive [''Ty, ''Flag, ''Register, ''Label, ''TyApp, ''Pack, 
          ''WordVal, ''SmallVal, ''HeapVal, ''Instruction, 
          ''InstrSeq])

------------------------------------------------------
instance Alpha Flag
instance Alpha Ty 
instance Alpha Register 
instance Alpha Label
instance Alpha a => Alpha (TyApp a)
instance Alpha a => Alpha (Pack a)
instance Alpha WordVal
instance Alpha SmallVal
instance Alpha HeapVal
instance Alpha Instruction
instance Alpha InstrSeq

-- need to replace this with a better instance
instance Alpha b => Alpha (Map Register b)

instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Ty Flag
instance (Subst Ty a) => Subst Ty (TyApp a)
instance (Subst Ty a) => Subst Ty (Pack a)
instance Subst Ty WordVal
instance Subst Ty SmallVal
instance Subst Ty HeapVal
instance Subst Ty Instruction
instance Subst Ty InstrSeq
instance Subst Ty Label
instance Subst Ty Register
instance (Rep a, Subst Ty b) => Subst Ty (Map a b) 

freshForHeap :: Heap -> Label
freshForHeap h = Label (ml, i+1) where
  Label (ml,i) = maximum (Map.keys h)

-----------------------------------------------------
-- operational semantics
-----------------------------------------------------

getIntReg :: RegisterFile -> Register -> Maybe Int
getIntReg r rs = do
  rsv <- Map.lookup rs r
  case rsv of 
    TmInt i -> Just i
    _ -> Nothing

getInt :: SmallVal -> Maybe Int
getInt (WordVal (TmInt i)) = Just i
getInt _ = Nothing

arith :: (Int -> Int -> Int) -> RegisterFile ->
  Register -> SmallVal -> Maybe WordVal
arith op r rs v = do
  i <- getIntReg r rs
  j <- getInt v
  return (TmInt (i `op` j))

-- R^(sv)
loadReg :: RegisterFile -> SmallVal -> M (WordVal, [Ty])
loadReg r (RegVal rs) = case Map.lookup rs r of
  Just w -> return (w, [])
  Nothing -> throwE "register val not found"
loadReg r (WordVal w) = return (w, [])
loadReg r (SApp (TyApp sv ty))   = do 
  (w, tys) <- loadReg r sv
  return (w, ty:tys)
loadReg r (SPack (Pack t1 sv t2)) = do 
  (w, tys) <- loadReg r sv         
  return (WPack (Pack t1 (tyApp w tys) t2), [])
  
tyApp :: WordVal -> [Ty] -> WordVal  
tyApp w [] = w
tyApp w (ty:tys) = tyApp (WApp (TyApp w ty)) tys
  
jmpReg :: Heap -> RegisterFile -> SmallVal -> M Machine
jmpReg h r v = do
 (w,tys) <- loadReg r v 
 case w of 
        LabelVal l ->
          case (Map.lookup l h) of
            Just (Code alphas gamma instrs') -> do
              when (length alphas /= length tys) $
                throwE "Bnz: wrong # type args"
              return (h, r, substs (zip alphas tys) instrs')
            _ -> throwE "Bnz: cannot jump, not code"  
        _ -> throwE "Bnz: cannot jump, not label"
                   
step :: Machine -> M Machine
step (h, r, Add rd rs v `Seq` instrs) = do
  case arith (+) r rs v of 
    Just v' -> return (h, Map.insert rd v' r, instrs)
    Nothing -> throwE "Cannot add"
step (h, r, Mul rd rs v `Seq` instrs) = do
  case arith (*) r rs v of
    Just v' -> return (h, Map.insert rd v' r, instrs)
    Nothing -> throwE "Cannot mul"
step (h, r, Sub rd rs v `Seq` instrs) = do
  case arith (-) r rs v of
    Just v' -> return (h, Map.insert rd v' r, instrs)
    Nothing -> throwE "Cannot sub"
step (h, r, Bnz rs v `Seq` instrs) = do
  case Map.lookup rs r of 
    Just (TmInt 0) -> return (h, r, instrs)
    Just (TmInt _) -> jmpReg h r v
step (h, r, Jump v) = jmpReg h r v
step (h, r, Ld rd rs i `Seq` instrs) = do
  case Map.lookup rs r of 
    Just (LabelVal l) -> 
      case Map.lookup l h of 
        Just (Tuple ws) | i < length ws -> 
          return (h, Map.insert rd (ws !! i) r, instrs)
        _ -> throwE "ld: Cannot load location"
    _ -> throwE "ld: not label"
step (h, r, Malloc rd tys `Seq` instrs) = do
  let l = freshForHeap h
  return (Map.insert l  (Tuple (map Junk tys))  h,
          Map.insert rd (LabelVal l) r, 
          instrs)
step (h, r, Mov rd v `Seq` instrs) = do    
  (w,tys) <- loadReg r v
  return (h, Map.insert rd (tyApp w tys) r, instrs)
step (h, r, St rd i rs `Seq` instrs) = do      
  case Map.lookup rs r of 
    Just w' ->
      case Map.lookup rd r of
        Just (LabelVal l) ->
          case Map.lookup l h of
            Just (Tuple ws) | i < length ws -> do
              let (ws0,(_:ws1)) = splitAt i ws
              return 
                (Map.insert l (Tuple (ws0 ++ (w':ws1))) h,
                 r, instrs)
            _ -> throwE "heap label not found or wrong val"
        _ -> throwE "register not found or wrong val"
    _ -> throwE "register not found"
step (h, r, Unpack alpha rd v `Seq` instrs) = do
  (w0, tys) <- loadReg r v
  case tyApp w0 tys of 
    WPack (Pack ty w _) ->
      return (h, Map.insert rd w r, subst alpha ty instrs)
    _ -> throwE "not a pack"
  
------------------------------------------------------
-- Helper functions
------------------------------------------------------

------------------------------------------------------
-- Typechecker
------------------------------------------------------

type Delta = [ TyName ]

data Ctx = Ctx { getDelta :: Delta , 
                 getGamma :: Gamma ,  
                 getPsi   :: Psi }
emptyCtx = Ctx { getDelta = [], 
                 getGamma = Map.empty, 
                 getPsi = Map.empty }

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    if List.elem v (getDelta g) then
      return ()
    else
      throwE $ "Type variable not found " ++ (show v)


extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : (getDelta ctx) }

extendTys :: [TyName] -> Ctx -> Ctx
extendTys ns ctx = foldr extendTy ctx ns

{-
lookupTmVar :: Ctx -> ValName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError $ "Term variable notFound " ++ (show v)

extendTm :: ValName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

extendTms :: [ValName] -> [Ty] -> Ctx -> Ctx
extendTms [] [] ctx = ctx
extendTms (n:ns) (ty:tys) ctx = extendTm n ty (extendTms ns tys ctx)
-}
{-
extendDecl :: Decl -> Ctx -> Ctx
extendDecl (DeclVar x (Embed (Ann _ ty))) = extendTm x ty
extendDecl (DeclPrj i x (Embed (Ann _ (TyProd tys)))) = extendTm x (tys !! i)                                           
extendDecl (DeclPrim x  _) = extendTm x TyInt
extendDecl (DeclUnpack b x (Embed (Ann _ (Exists bnd)))) = 
  extendTy b . extendTm x (patUnbind b bnd)
-}

-- tau is a well-formed type
tcty :: Ctx -> Ty -> M ()
tcty ctx  (TyVar x) =
   checkTyVar ctx x
tcty ctx  (All b) = do
   (xs, reg) <- unbind b
   let ctx' = extendTys xs ctx 
   tcGamma ctx' reg
tcty ctx TyInt =  return ()
tcty ctx (TyProd tys) = do
   mapM_ (tcty ctx . fst) tys
tcty ctx (Exists b) = do 
  (a, ty) <- unbind b
  tcty (extendTy a ctx) ty

-- Psi is a well-formed heap type
tcPsi :: Ctx -> Psi -> M ()
tcPsi ctx psi = mapM_ (tcty ctx) (Map.elems psi)
                                 
-- Gamma is a well-formed register file
tcGamma :: Ctx -> Gamma -> M ()
tcGamma ctx g = mapM_ (tcty ctx) (Map.elems g)

-- t1 is a subtype of t2
subtype :: Ctx -> Ty -> Ty -> M ()
subtype ctx (TyVar x) (TyVar y) | x == y = return ()
subtype ctx TyInt TyInt = return ()
subtype ctx (All bnd1) (All bnd2) = do
  Just (vs1, g1, vs2, g2) <- unbind2 bnd1 bnd2
  subGamma ctx g1 g2
  
subGamma :: Ctx -> Gamma -> Gamma -> M ()
subGamma = undefined

{-
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
     else throwError $ "wrong annotation on: " ++ pp v ++ "\nInferred: " ++ pp ty' ++ "\nAnnotated: " ++ pp ty 

typecheckDecl g (DeclVar x (Embed av)) = do
  ty <- typecheckAnnVal g av
  return $ extendTm x ty g
typecheckDecl g (DeclPrj i x (Embed av@(Ann v _))) = do
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
typecheckDecl g (DeclAssign x (Embed (av1@(Ann v1 _), i, av2))) = do
  ty1 <- typecheckAnnVal g av1 
  ty2 <- typecheckAnnVal g av2
  case ty1 of 
    TyProd tys | i < length tys -> 
      let (xs,(ty,_):ys) = splitAt i tys in
      if ty `aeq` ty2 
        then return $ extendTm x (TyProd (xs ++ (ty,Init) : ys)) g
        else throwError "TypeError"
         
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
    return $ parens (da <> text ":" <> dt)  -}
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
-}