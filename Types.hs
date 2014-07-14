{-#
  LANGUAGE GADTs
  , GeneralizedNewtypeDeriving
  , LambdaCase
  #-}

module Types
  ( Cell
  , Constant(..)
  , Depth(..)
  , Labelled(..)
  , Register(..)
  , Target(..)
  ) where

import Compiler.Hoopl hiding ((<*>))
import Data.Int

-- | A memory cell in the virtual machine.
type Cell = Int64

-- | A thing indexed with a control flow graph label.
data Labelled a = Labelled { labelledLabel :: !Label, labelledValue :: !a }
  deriving (Eq, Ord, Show)

-- | A constant integer in the input program.
newtype Constant = Constant Cell
  deriving (Eq, Ord)

instance Show Constant where
  show (Constant c) = show c

-- | A depth on the stack.
newtype Depth = Depth Int
  deriving (Show)

-- | A jump target in the input program.
newtype Target = Target Int
  deriving (Enum, Eq, Ord, Show)

-- | A register name.
newtype Register = Register Int
  deriving (Eq, Ord)

instance Show Register where
  show (Register r) = '$' : show r
