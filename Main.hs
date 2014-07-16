{-#
  LANGUAGE OverloadedStrings
  , FlexibleContexts
  , FlexibleInstances
  , GADTs
  , GeneralizedNewtypeDeriving
  , LambdaCase
  , NoMonomorphismRestriction
  , ScopedTypeVariables
  , TypeFamilies
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Compiler.Hoopl hiding ((<*>))
import Control.Exception hiding (try)
import System.Environment
import System.IO.Error

import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector

import Flatten
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
          Left message -> error $ show message
          Right parsed -> do
            let (program, entry, depths) = unflatten parsed
            optimized <- optimize entry program depths
            return (optimized, entry)
      let (flattened, entry') = flatten entry optimized
      result <- run entry' flattened
        . Vector.fromList $ map read rawMachineArgs
      print result

      where
      missing e = if isDoesNotExistError e
        then bug $ concat
          [ "System.IO.FileNotFoundException: Could not find file \""
          , filename
          , "\""
          ]
        else throwIO e
