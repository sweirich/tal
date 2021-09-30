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

-- Run a few test cases that produce int values
main :: IO ()
main = do
    checkInt "1+1" (test F.onePlusOne) 2
    checkInt "two" (test F.two) 2
    checkInt "6!" (test F.sixfact) 720

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

checkInt :: String -> TAL.WordVal -> Int -> IO ()
checkInt name actual expected = do
    case actual of 
        TAL.TmInt y -> 
            unless (y == expected) $ do
                putStrLn $ name ++ " returned:" ++ pp y
                exitFailure
        wv -> do
            putStrLn $ name ++ " returned: " ++ pp wv
            exitFailure
    putStrLn $ "Test passed: " ++ name


printM :: (Display a) => M a -> IO ()
printM x = putStrLn $ pp $ runM x

printK :: F.Tm -> IO ()
printK f = do 
   putStrLn "--- K ---"
   printM $ do af <- F.typecheck F.emptyCtx f
               Translate.toProgK af

printC :: F.Tm -> IO ()
printC f = do 
    putStrLn "--- C ---"            
    printM $ do af <- F.typecheck F.emptyCtx f
                k <- Translate.toProgK af
                Translate.toProgC k

printH :: F.Tm -> IO ()
printH f = do
    putStrLn "--- H ---"    
    printM $ do af <- F.typecheck F.emptyCtx f
                k <- Translate.toProgK af
                c <- Translate.toProgC k
                Translate.toProgH c

printA :: F.Tm -> IO ()
printA f = do 
    putStrLn "--- A ---"    
    printM $ do af <- F.typecheck F.emptyCtx f
                k <- Translate.toProgK af
                c <- Translate.toProgC k
                h <- Translate.toProgH c
                Translate.toProgA h

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
