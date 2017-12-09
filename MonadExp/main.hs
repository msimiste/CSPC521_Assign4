module Main where

import System.Environment
import Data.List
import Data.Maybe
import Control.Monad.State

type MyState = Int
startState = 0


counter:: State (Int, Int) ()
counter = do
    (a,num) <- get
    put (a, num + 1)
    
dec:: State (Int, Int) ()
dec = do
    (num,a) <- get
    put (num + 1,a)
    


getInput n = do
    putStrLn  "Enter yes or no"
    input <- getLine
    case (input) of
        ("YES") -> do
                    let res = runState counter n
                    putStrLn (show res)
                    getInput (snd res)                   
        ("NO") -> do
                    let res = runState dec n
                    putStrLn (show res)
                    getInput(snd res)
        _ -> getInput n
    getInput n
    
main = do getInput (0,0)


