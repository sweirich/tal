module Util(
  -- ** Local
  patUnbind,
  Prim(..),evalPrim,M,runM,

  pp, Display(..), DM(..), displayList, displayTuple, intersperse, prefix, withPrec, precedence, binop,

  -- * GHC.Generics
  Generic(..),
  
  Set, Map,
  -- ** PrettyPrint
  Doc, (<+>), ($$), ($+$), int, punctuate, comma, colon, text, nest, vcat, sep, parens, braces, brackets) where

import Text.PrettyPrint (Doc, (<+>), ($$), ($+$), vcat, int, punctuate, nest,
                          comma, colon, text, sep, parens, braces, brackets, empty,
                          render)
import qualified Text.PrettyPrint as PP
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Trans.Except
import Control.Monad.Reader
import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Map(Map)
import qualified Data.Map as Map

import GHC.Generics (Generic(..))
import Unbound.Generics.LocallyNameless hiding (prec,empty,Data,Refl,Val)
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind


------------------
-- should move to Unbound.LocallyNameless.Ops
-- ? what if the pattern binds the wrong number of variables???

patUnbind :: (Alpha p, Alpha t) => p -> Bind p t -> t
patUnbind p b = case b of
                  (B _ t) -> open initialCtx (nthPatFind p) t

------------------

-- need to replace this with a better instance
instance (Show a, Ord a, Ord b, Alpha b) => Alpha (Map a b) where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = error "TAL: TODO"

  close ctx b = Map.map (close ctx b)
  open ctx b = Map.map (open ctx b)

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = error "TAL: Don't use a finite map as a pattern"
  namePatFind _ = error "TAL: Don't use a finite map as a pattern"

  swaps' ctx p = Map.map (swaps' ctx p)
                          
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j
  
instance (Alpha b, Subst ty b) => Subst ty (Map a b) where
  subst n u m = Map.map (subst n u) m
  substs ss m = Map.map (substs ss) m


-------------------------------------------------------------------------
-- Primitives
-------------------------------------------------------------------------

data Prim = Plus | Minus | Times deriving (Eq, Ord, Generic)

instance Show Prim where
  show Plus  = "+"
  show Minus = "-"
  show Times = "*"


instance Alpha Prim

evalPrim :: Prim -> Int -> Int -> Int
evalPrim Plus  = (+)
evalPrim Times = (*)
evalPrim Minus = (-)


-------------------------------------------------------------------------
-- Monad for evaluation, typechecking and translation.
-------------------------------------------------------------------------

type M = ExceptT String FreshM

runM :: M a -> a
runM m = case runFreshM (runExceptT m) of
   Left s  -> error s
   Right a -> a


-------------------------------------------------------------------------
-- The Display class and other pretty printing helper functions
-------------------------------------------------------------------------

-- | pretty-print                  
pp :: Display t => t -> String
pp d = render (runIdentity (runReaderT (runDM (display d)) initDI))
   
class Display t where
  -- | Convert a value to a 'Doc'.
  display  :: t -> DM Doc   
   
newtype DM a = DM { runDM :: (ReaderT DispInfo Identity) a } 
             deriving (Functor,Applicative,Monad)



maybeParens :: Bool -> Doc -> Doc
maybeParens b d = if b then parens d else d
   
   
prefix :: String -> Doc -> DM Doc   
prefix str d = do
  di <- ask
  return $ maybeParens (precedence str < prec di) (PP.text str <+> d)
   
binop :: Doc -> String -> Doc -> DM Doc
binop d1 str d2 = do 
  di <- ask
  let dop = if str == " " then sep [d1, d2] else sep [d1, PP.text str, d2]
  return $ maybeParens (precedence str < prec di) dop

   
   
precedence :: String -> Int   
precedence "->" = 10
precedence " "  = 10
precedence "forall" = 9
precedence "if0"    = 9
precedence "fix"    = 9
precedence "\\"     = 9
precedence "*"  = 8
precedence "+"  = 7
precedence "-"  = 7
precedence  _   = 0
   


instance MonadReader DispInfo DM where
  ask     = DM ask
  local f (DM m) = DM (local f m) 

-- | The data structure for information about the display
-- 
data DispInfo = DI
  {
  prec       :: Int,              -- ^ precedence level  
  showTypes  :: Bool,             -- ^ should we show types?  
  dispAvoid  :: Set.Set AnyName   -- ^ names that have been used
  }

instance LFresh DM where
  lfresh nm = do
      let s = name2String nm
      di <- ask;
      return $ head (filter (\x -> AnyName x `Set.notMember` dispAvoid di)
                      (map (makeName s) [0..]))
  getAvoids = asks dispAvoid
  avoid names = local upd where
     upd di = di { dispAvoid = 
                      Set.fromList names `Set.union` dispAvoid di }


-- | An empty 'DispInfo' context
initDI :: DispInfo
initDI = DI 10 False Set.empty

withPrec :: Int -> DM a -> DM a
withPrec i = 
  local $ \ di -> di { prec = i }
                  
getPrec :: DM Int                  
getPrec = asks prec 
  
  
  
intersperse             :: Doc -> [Doc] -> [Doc]
intersperse _   []      = []
intersperse _   [x]     = [x]
intersperse sep (x:xs)  = x <> sep : intersperse sep xs

displayList :: Display t => [t] -> DM Doc  
displayList es = do
  ds <- mapM (withPrec 0 . display) es
  return $ PP.cat (intersperse PP.comma ds)
  
displayTuple :: Display t => [t] -> DM Doc  
displayTuple es = do  
  ds <- displayList es
  return $ PP.text "<" <> ds <> PP.text ">"  

--------------------------------------------

instance Display (Name a) where
  display n = return $ (PP.text . show) n
  
--------------------------------------------

instance Display String where
  display = return . PP.text
instance Display Int where
  display = return . PP.text . show
instance Display Integer where
  display = return . PP.text . show
instance Display Double where
  display = return . PP.text . show
instance Display Float where
  display = return . PP.text . show
instance Display Char where
  display = return . PP.text . show
instance Display Bool where
  display = return . PP.text . show

