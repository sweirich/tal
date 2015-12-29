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

reg0 :: Register
reg0 = Register "r0"

instance Enum Register where
  toEnum i = Register ("r" ++ show i)
  fromEnum (Register ('r' : str)) = read str

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

lookupHeapLabel :: Ctx -> Label -> M Ty
lookupHeapLabel ctx v = do
    case Map.lookup v (getPsi ctx) of
      Just s -> return s
      Nothing -> throwE $ "Label not found " ++ (show v)

lookupReg :: Ctx -> Register -> M Ty
lookupReg ctx v = do
    case Map.lookup v (getGamma ctx) of
      Just s -> return s
      Nothing -> throwE $ "Register not found " ++ (show v)

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
-- Only uses D 
tcPsi :: Ctx -> Psi -> M ()
tcPsi ctx psi = mapM_ (tcty ctx) (Map.elems psi)
                                 
-- Gamma is a well-formed register file
-- D |- G
tcGamma :: Ctx -> Gamma -> M ()
tcGamma ctx g = mapM_ (tcty ctx) (Map.elems g)

-- t1 is a subtype of t2
-- D |- t1 <= t2 
subtype :: Ctx -> Ty -> Ty -> M ()
subtype ctx (TyVar x) (TyVar y) | x == y = return ()
subtype ctx TyInt TyInt = return ()
subtype ctx (All bnd1) (All bnd2) = do
  Just (vs1, g1, vs2, g2) <- unbind2 bnd1 bnd2
  subGamma ctx g1 g2
  
-- D |- G1 <= G2  
subGamma :: Ctx -> Gamma -> Gamma -> M ()
subGamma ctx g1 g2 = do
  mapM_ (\(r, t2) -> case Map.lookup r g1 of 
            Just t1 -> subtype ctx t1 t1 
            Nothing -> throwE $ "register not found:" ++ show r) 
    (Map.assocs g2)
    
-- |- H : Psi    
typeCheckHeap :: Heap -> Psi -> M ()
typeCheckHeap h psi = mapM_ tcHeapDecl (Map.assocs h) where
  ctx = emptyCtx { getPsi = psi } 
  
  tcHeapDecl :: (Label, HeapVal) -> M ()
  tcHeapDecl (l,hv) = 
    case Map.lookup l psi of
      Just ty -> tcHeapVal hv ty
      Nothing -> throwE $ "heap type not found:" ++ show l
      
  tcTuple (Junk ty', (ty,Un)) = 
    -- maybe we know these are the same already?
    subtype ctx ty' ty
  tcTuple (wv, (ty,Init)) = do
     ty' <- tcWordVal ctx wv 
     subtype ctx ty' ty 
     
  tcHeapVal (Tuple wvs) (TyProd tys) | length wvs == length tys = do
    mapM_ tcTuple (zip wvs tys)
            
  tcHeapVal (Code as g is) _ = do
    -- TODO: better error message. What if wrong # binders?
    -- let g' = patUnbind as bnd
    -- check (All bnd) ??
    let ctx = Ctx as g psi
    tcInstrSeq ctx is
  tcHeapVal _ _ = throwE $ "wrong type for heap val"

tcWordVal :: Ctx -> WordVal -> M Ty
tcWordVal ctx (LabelVal l) = lookupHeapLabel ctx l
tcWordVal ctx (TmInt i)    = return TyInt
tcWordVal ctx (Junk ty')   = throwE $ "BUG: no Junk here"
tcWordVal ctx (WApp tapp) = tcApp tcWordVal ctx tapp
tcWordVal ctx (WPack pack) = tcPack tcWordVal ctx pack

tcApp :: (Ctx -> a -> M Ty) -> Ctx -> TyApp a -> M Ty
tcApp f ctx (TyApp wv ty) = do
  tcty ctx ty
  ty' <- f ctx wv
  case ty' of 
    All bnd -> do 
      (as, bs) <- unbind bnd
      case as of 
        [] -> throwE "can't instantiate non-polymorphic function"
        (a:as') -> do
          let bs' = subst a ty bs
          return (All (bind as' bs'))

tcPack :: (Ctx -> a -> M Ty) -> Ctx -> Pack a -> M Ty 
tcPack f ctx (Pack ty1 wv ty) = do
  case ty of 
    Exists bnd -> do 
      (a, ty2) <- unbind bnd
      tcty ctx ty1
      ty' <- f ctx wv
      if (not (ty' `aeq` subst a ty1 ty2)) 
         then throwE "type error"
         else return ty    
              
tcSmallVal :: Ctx -> SmallVal -> M Ty              
tcSmallVal ctx (RegVal r)   = lookupReg ctx r 
tcSmallVal ctx (WordVal wv) = tcWordVal ctx wv
tcSmallVal ctx (SApp app)   = tcApp tcSmallVal ctx app
tcSmallVal ctx (SPack pack) = tcPack tcSmallVal ctx pack

tcInstrSeq :: Ctx -> InstrSeq -> M ()
tcInstrSeq ctx (Seq i is) = do 
  ctx' <- tcInstr ctx i
  tcInstrSeq ctx' is
tcInstrSeq ctx (Jump sv)  = do
  ty <- tcSmallVal ctx sv
  case ty of 
    All bnd -> 
      let g = patUnbind [] bnd in
      subGamma ctx g (getGamma ctx)
tcInstrSeq ctx (Halt ty)  = do
  ty' <- lookupReg ctx reg0 
  subtype ctx ty ty' 

tcArith :: Ctx -> Register -> Register -> SmallVal -> M Ctx
tcArith ctx rd rs sv = do
      ty1 <- lookupReg ctx rs
      ty2 <- tcSmallVal ctx sv
      unless (ty1 `aeq` TyInt) $ throwE "source reg must be int" 
      unless (ty2 `aeq` TyInt) $ throwE "immediate must be int"
      let g' = Map.insert rd TyInt (getGamma ctx) 
      return (ctx { getGamma = g' })

tcInstr :: Ctx -> Instruction -> M Ctx
tcInstr ctx i = case i of
    (Add rd rs sv) -> tcArith ctx rd rs sv
    (Bnz r sv) -> do 
      ty1 <- lookupReg ctx r
      ty2 <- tcSmallVal ctx sv
      unless (ty1 `aeq` TyInt) $ throwE "source reg must be int" 
      case ty2 of
        All bnd -> do
          let g = patUnbind [] bnd 
          subGamma ctx (getGamma ctx) g
          return ctx  
        _ -> throwE "must bnz to code label"
            
    (Ld  rd rs i) -> do
      ty1 <- lookupReg ctx rs
      case ty1 of 
        TyProd tyfs -> do
          when (i >= length tyfs) $ throwE "Ld: index out of range"
          let (ty,f) = tyfs !! i
          unless (f == Init) $ throwE "Ld: load from unitialized field"
          let g = Map.insert rd ty (getGamma ctx)
          return $ ctx { getGamma = g } 
        _ -> throwE $ "Ld: not a tuple"
              
    (Malloc rd tys) -> do 
      let ty = TyProd (map (,Un) tys)
      let g = Map.insert rd ty (getGamma ctx)
      return $ ctx { getGamma = g }    
      
    (Mov rd sv) -> do
      ty <- tcSmallVal ctx sv
      let g = Map.insert rd ty (getGamma ctx)
      return $ ctx { getGamma = g }    
      
    (Mul rd rs sv) -> tcArith ctx rd rs sv
    
    (St rd i rs) -> do
      ty1 <- lookupReg ctx rd
      ty2 <- lookupReg ctx rs
      case ty1 of 
        TyProd tyfs -> do
          when (i >= length tyfs) $ throwE "St: index out of range"
          let (before, _:after) = List.splitAt i tyfs
          let ty = TyProd (before ++ [(ty2,Init)] ++ after)
          let g = Map.insert rd ty (getGamma ctx)    
          return $ ctx { getGamma = g }
        _ -> throwE $ "St: rd not a tuple"
              
    (Sub rd rs sv) -> tcArith ctx rd rs sv
    
    (Unpack a rd sv) -> do
      when (a `elem` getDelta ctx) $ throwE "Unpack: tyvar not fresh"
      ty1 <- tcSmallVal ctx sv
      case ty1 of 
        Exists bnd -> do
          let ty = patUnbind a bnd
          let g = Map.insert rd ty (getGamma ctx)    
          return $ ctx { getDelta = a : (getDelta ctx) }{ getGamma = g }

         
progcheck :: Machine -> M ()         
progcheck (heap, regfile, is) = do
  let getHeapTy (_,Tuple _ )    = throwE $ "only code to start"
      getHeapTy (l,Code as g _) = return $ (l,All (bind as g))
  psi_assocs <- mapM getHeapTy (Map.assocs heap)
  let psi = Map.fromList psi_assocs
  unless (Map.null regfile) $ throwE "must start with empty registers"
  let ctx = Ctx [] Map.empty psi
  tcPsi ctx psi
  tcInstrSeq ctx is

-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display (TyVar n)     = display n
  display (TyInt)       = return $ text "Int"
  display (All bnd) = lunbind bnd $ \ (as,g) -> do
    da <- displayList as
    dt <- display g
    if null as 
      then return dt 
      else prefix "forall" (brackets da <> text "." <+> dt)
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
    
instance Display (Map Register Ty) where
  display m = do
    fcns <- mapM (\(r,v) -> do 
                     dv <- display v
                     return (r, dv)) (Map.toList m)
    return $ braces (sep [ text (show n) 
                           <+> text "=" <+> dv | (n,dv) <- fcns ])

instance Display a => Display (Pack a) where
  display (Pack ty e _) = do 
    dty <- display ty
    de  <- display e 
    prefix "pack" (brackets (dty <> comma <> de))

instance Display a => Display (TyApp a) where
  display (TyApp av ty) = do
    dv <- display av
    dt <- display ty
    return $ dv <+> (brackets dt)

instance Display WordVal where                         
  display (LabelVal l) = return $ text ( show l)
  display (TmInt i) = return $ int i
  display (Junk ty) = return $ text "?"
  display (WPack p) = display p
  display (WApp  a) = display a

instance Display SmallVal where                         
  display (RegVal r)  = return (text $ show r)
  display (WordVal n) = display n
  display (SPack p) = display p
  display (SApp  a) = display a


instance Display HeapVal where
  display (Code as gamma is) = do
    ds    <- displayList as  
    dargs <- display gamma
    de    <- withPrec (precedence "code") $ display is
    let tyArgs = if null as then empty else brackets ds
    prefix "code"  (tyArgs <> dargs <> text "." $$ de)
    
  display (Tuple es) = displayTuple es

dispArith str rd rs sv = do
  dv <- display sv
  return $ text str <+> text (show rd) 
    <> comma <> text (show rs) <> comma <+> dv

instance Display Instruction where
  display i = case i of 
    Add rd rs sv -> dispArith "add" rd rs sv
    Bnz r sv  -> do
                 dv <- display sv
                 return $ text "bnz" <+> text (show r) <> comma <> dv
      
    (Ld  rd rs i) -> 
      return $ text "ld" <+> text (show rd) <> comma <> text (show rs) 
               <> brackets (int i)
      
    (Malloc rd tys) -> do 
      dtys <- displayList tys
      return $ text "malloc" <+> text (show rd) <> comma <> brackets dtys
      
    (Mov rd sv) -> do
      dv <- display sv
      return $ text "mov" <+> text (show rd) <> comma <> dv
      
    (Mul rd rs sv) -> dispArith "mul" rd rs sv
    
    (St rd i rs) -> do
      return $ text "st" <+> text (show rd) <> brackets (int i) <> comma 
              <> text (show rs)
      
    (Sub rd rs sv) -> dispArith "sub" rd rs sv
    
    (Unpack a rd sv) -> do
      dv <- display sv
      return $ text "unpack" 
        <> brackets (text (show a) <> comma <> text (show rd))
        <> comma <> dv

instance Display InstrSeq where
  display (Seq i is) = do
    di  <- display i 
    dis <- display is 
    return $ di $+$ dis
  display (Jump sv) = do 
    ds <- display sv
    return $ text "jmp" <+> ds
  display (Halt _) = do 
    return $ text "halt" 


instance Display Label where
  display l = return (text (show l))

instance Display a => Display (Map Label a) where
  display m = do
    fcns <- mapM (\(d,v) -> do 
                     dn <- display d
                     dv <- display v
                     return (dn, dv)) (Map.toList m)
    return $ vcat [ n <+> text "=" <+> dv | (n,dv) <- fcns ]
    
{-
instance Display (Tm, Heap) where
  display (tm,h) = do
    dh <- display h
    dt <- display tm
    return $ dh $$ text "in" <+> dt
-}