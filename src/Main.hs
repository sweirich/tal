module Main where

import Util ( pp, runM, Display, M )
import qualified Data.Map as Map
import qualified F
import qualified K
import qualified C
import qualified A
import qualified TAL
import qualified Translate
import Control.Monad.Except ( MonadError(throwError), unless )

import System.Exit (exitFailure)

main :: IO ()
main = do
    t1
    t2
    t3
    t4
    t5
    let wv = test F.sixfact
    case test F.sixfact of 
        TAL.TmInt y -> 
            unless (y == 120) $ do
                putStrLn $ "6! returned: " ++ pp y
                exitFailure
        wv -> do
            putStrLn $ "6! returned: " ++ pp wv
            exitFailure
    putStrLn "6! test passed."

-------------------------------
-- Helper functions for testing
-------------------------------
test :: F.Tm -> TAL.WordVal
test f = runM $ do
  tal  <- Translate.compile f
  (h, r, _) <- TAL.run tal
  case Map.lookup TAL.reg1 r of
    Just v -> return v
    Nothing -> throwError "no result!"

printM :: (Display a) => M a -> IO ()
printM x = putStrLn $ pp $ runM x

t1 = do
    print "Compiling 1 + 1"
    printM $ return F.onePlusOne
    printM $ Translate.compile F.onePlusOne

t2 = do
    print "Compiling 2"
    printM $ return F.two
    printM $ Translate.compile F.two

t3 = do
    print "Compiling ctrue"
    printM $ return F.ctrue 
    printM $ Translate.compile F.ctrue

t4 = do
    print "Compiling 6!"
    printM $ return F.sixfact
    printM $ Translate.compile F.sixfact

t5 = do
    print "Compiling twice"
    printM $ return F.twice
    printM $ Translate.compile F.twice
