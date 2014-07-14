{-#
  LANGUAGE OverloadedStrings
  , BangPatterns
  , FlexibleContexts
  , FlexibleInstances
  , GADTs
  , GeneralizedNewtypeDeriving
  , LambdaCase
  , NoMonomorphismRestriction
  , PatternGuards
  , RecordWildCards
  , ScopedTypeVariables
  , StandaloneDeriving
  , TypeFamilies
  , ViewPatterns
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Compiler.Hoopl hiding ((<*>))
import Control.Exception hiding (try)
import System.Environment
import System.IO.Error

import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector

import Debug.Trace

import Optimize
import Parse
import Run
import Unflatten
import Utils

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> bug "System.IndexOutOfRangeException: Array index is out of range."
    filename : rawMachineArgs -> do
      file <- Lazy.readFile filename `catch` missing
      (optimized, entry) <- return . runSimpleUniqueMonad $ do
        parseResult <- parse filename file
        case parseResult of
          (_, Left message) -> error $ show message
          (_idMap, Right parsed) -> do
            let (program, entry) = unflatten parsed
            !_ <- trace "Input: " (return ())
            !_ <- trace (showGraph show program) (return ())
            optimized <- optimize entry program
            !_ <- trace ("\nOptimized: ") (return ())
            !_ <- trace (showGraph show optimized) (return ())
            return (optimized, entry)
      result <- run entry optimized $ Vector.fromList (map read rawMachineArgs)
      print result
      where
      missing e = if isDoesNotExistError e
        then bug $ concat
          [ "System.IO.FileNotFoundException: Could not find file \""
          , filename
          , "\""
          ]
        else throwIO e
