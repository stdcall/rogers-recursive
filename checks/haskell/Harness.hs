-- | The harness of the executable checks of the book: named groups of
-- checks, a stop at the first failure (non-zero exit), the line
-- "ok <scope>: N checks" at the end, the counts per group with --verbose.
module Harness (Counter, newCounter, group, finish) where

import Control.Monad (forM_, unless, when)
import Data.IORef
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush, hPutStrLn, stderr, stdout)

data Counter = Counter (IORef Int) (IORef [(String, Int)])

newCounter :: IO Counter
newCounter = Counter <$> newIORef 0 <*> newIORef []

-- | Run a named group of checks; stop at the first failure.
group :: Counter -> String -> [(String, Bool)] -> IO ()
group (Counter total groups) name cs = do
  n <- go 0 cs
  modifyIORef' total (+ n)
  modifyIORef' groups (++ [(name, n)])
  args <- getArgs
  when ("--verbose" `elem` args) $ do
    putStrLn (show n ++ "\t" ++ name)
    hFlush stdout
  where
    go :: Int -> [(String, Bool)] -> IO Int
    go k [] = return k
    go k ((what, ok) : rest) = do
      unless ok $ do
        hPutStrLn stderr ("FAILED [" ++ name ++ "] " ++ what)
        exitFailure
      let k' = k + 1
      k' `seq` go k' rest

finish :: Counter -> String -> IO ()
finish (Counter total groups) scope = do
  n <- readIORef total
  gs <- readIORef groups
  forM_ [g | (g, 0) <- gs] (\g -> hPutStrLn stderr ("empty group: " ++ g))
  unless (all ((> 0) . snd) gs) exitFailure
  putStrLn ("ok " ++ scope ++ ": " ++ show n ++ " checks")
