{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Util where

import Text.PrettyPrint as PP
import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Trans.Except
import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Data.List as List

import Unbound.LocallyNameless hiding (prec,empty,Data,Refl,Val)
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Types

------------------
-- should move to Unbound.LocallyNameless.Ops
patUnbind :: (Alpha p, Alpha t) => p -> Bind p t -> t
patUnbind p (B _ t) = openT p t
------------------


-------------------------------------------------------------------------
-- Primitives
-------------------------------------------------------------------------

data Prim = Plus | Minus | Times deriving (Eq, Ord)

instance Show Prim where
  show Plus  = "+"
  show Minus = "-"
  show Times = "*"

$(derive [''Prim])

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
runM m = case (runFreshM (runExceptT m)) of
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
  return $ maybeParens (precedence str < prec di) (text str <+> d)
   
binop :: Doc -> String -> Doc -> DM Doc
binop d1 str d2 = do 
  di <- ask
  let dop = if str == " " then sep [d1, d2] else sep [d1, text str, d2]
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
      return $ head (filter (\x -> AnyName x `Set.notMember` (dispAvoid di))
                      (map (makeName s) [0..]))
  getAvoids = dispAvoid <$> ask
  avoid names = local upd where
     upd di = di { dispAvoid = 
                      (Set.fromList names) `Set.union` (dispAvoid di) }


-- | An empty 'DispInfo' context
initDI :: DispInfo
initDI = DI 10 False Set.empty

withPrec :: Int -> DM a -> DM a
withPrec i = 
  local $ \ di -> di { prec = i }
                  
getPrec :: DM Int                  
getPrec = do
  di <- ask
  return (prec di)
  
  
intersperse             :: Doc -> [Doc] -> [Doc]
intersperse _   []      = []
intersperse _   [x]     = [x]
intersperse sep (x:xs)  = x <> sep : intersperse sep xs

displayList :: Display t => [t] -> DM Doc  
displayList es = do
  ds <- mapM (withPrec 0 . display) es
  return $ cat (intersperse comma ds)
  
displayTuple :: Display t => [t] -> DM Doc  
displayTuple es = do  
  ds <- displayList es
  return $ text "<" <> ds <> text ">"  

--------------------------------------------

instance Rep a => Display (Name a) where
  display n = return $ (text . show) n
  
--------------------------------------------

instance Display String where
  display = return . text
instance Display Int where
  display = return . text . show
instance Display Integer where
  display = return . text . show
instance Display Double where
  display = return . text . show
instance Display Float where
  display = return . text . show
instance Display Char where
  display = return . text . show
instance Display Bool where
  display = return . text . show

