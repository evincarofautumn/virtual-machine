{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import Control.Applicative
import Control.Exception hiding (try)
import Data.Function
import Data.IORef
import Data.Int
import Data.Vector (Vector)
import System.Environment
import System.Exit
import System.IO
import System.IO.Error
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Text.Lazy ()

import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as Mutable

-- import Debug.Trace

-- | An instruction in the input program.
data Instruction
  = Add Register Register Register
  | Call Offset Depth Register
  | Equals Register Register Register
  | Jump Offset
  | JumpIfZero Register Offset
  | LessThan Register Register Register
  | Move Register Register
  | Multiply Register Register Register
  | Negate Register Register
  | Not Register Register
  | Return Register
  | Set Register Constant
  deriving (Show)

-- | A constant integer in the input program.
newtype Constant = Constant Cell
  deriving (Show)

-- | A depth on the stack.
newtype Depth = Depth Int
  deriving (Show)

-- | An offset between instructions in the input program.
newtype Offset = Offset Int
  deriving (Show)

-- | A register name.
newtype Register = Register Int
  deriving (Show)

newtype InputProgram = InputProgram (Vector Instruction)
  deriving (Show)

type Cell = Int64

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> bug "System.IndexOutOfRangeException: Array index is out of range."
    filename : rawMachineArgs -> do
      file <- Lazy.readFile filename `catch` missing
      -- Text.putStrLn file
      case readProgram filename file of
        Left message -> hPrint stderr message >> exitFailure
        Right program -> do
          result <- run program $ Vector.fromList (map read rawMachineArgs)
          print result
      where
      missing e = if isDoesNotExistError e
        then bug $ concat
          [ "System.IO.FileNotFoundException: Could not find file \""
          , filename
          , "\""
          ]
        else throwIO e

readProgram :: SourceName -> Lazy.Text -> Either ParseError InputProgram
readProgram = parse program
  where
  program = InputProgram . Vector.fromList <$> (statement `sepEndBy` many1 newline)
  statement = horizontals *> unsigned >>= instruction
  instruction pc = choice
    [ Add <$ (word "Add") <*> registerComma <*> registerComma <*> register
    , Call <$ (word "Call") <*> (offset pc <* comma) <*> (depth <* comma) <*> register
    , register3 (word "Equals") Equals
    , try $ Jump <$ word "Jump" <*> offset pc
    , JumpIfZero <$ (word "JumpIfZero") <*> registerComma <*> offset pc
    , register3 (word "LessThan") LessThan
    , try $ register2 (word "Move") Move
    , register3 (word "Multiply") Multiply
    , try $ register2 (word "Negate") Negate
    , register2 (word "Not") Not
    , Return <$ word "Return" <*> register
    , Set <$ word "Set" <*> registerComma <*> constant
    ]
  digits = lexeme (many1 digit) <?> "number"
  offset pc = Offset . subtract pc <$> unsigned <?> "offset"
  unsigned = read <$> digits
  signed = (negate <$ char '-' <|> pure id) <*> unsigned
  depth = Depth <$> unsigned
  constant = Constant <$> signed
  register = char '$' *> (Register <$> signed)
  register2 mnemonic constructor
    = constructor <$ mnemonic <*> registerComma <*> register
  register3 mnemonic constructor
    = constructor <$ mnemonic <*> registerComma <*> registerComma <*> register
  registerComma = register <* comma
  lexeme = (<* horizontals)
  word = lexeme . string
  comma = word ","
  horizontal = oneOf " \t"
  horizontals = many horizontal

run :: InputProgram -> Vector Cell -> IO Cell
run (InputProgram instructions) machineArguments = do
  cs <- Mutable.new callStackSize
  vs <- Mutable.new valueStackSize
  csp <- newIORef (0 :: Int)
  vsp <- newIORef (0 :: Int)
  pc <- newIORef (0 :: Int)

  let
    push s sp value = do
      sp' <- readIORef sp
      Mutable.unsafeWrite s sp' value
      modifyIORef' sp succ
    pushValue = push vs vsp
    pushCall = push cs csp
    binary f out left right = do
      value <- f <$> readRegister left <*> readRegister right
      writeRegister out value
    unary f out in_ = writeRegister out . f =<< readRegister in_
    writeRegister (Register n) x
      = registerOffset n >>= \n' -> Mutable.unsafeWrite vs n' x
    readRegister (Register n) = Mutable.unsafeRead vs =<< registerOffset n
    registerOffset n = (+) <$> readIORef vsp <*> pure n
    jump (Offset offset) = modifyIORef' pc (+ offset) >> return Resume
    proceed = return Proceed
    halt = return . Halt
    enter frame@(StackFrame _ (Depth depth) _) = do
      pushCall frame
      modifyIORef' vsp (+ depth)

    -- Invariant: call stack is not empty.
    leave = do
      frame@(StackFrame _ (Depth depth) _) <- Mutable.unsafeRead cs . pred =<< readIORef csp
      modifyIORef' vsp (subtract depth)
      modifyIORef' csp pred
      return frame

    bool :: Bool -> Cell
    bool = fromIntegral . fromEnum

  Vector.mapM_ pushValue machineArguments

  fix $ \loop -> do
    instruction <- (instructions Vector.!) <$> readIORef pc

    {-
    do
      pc' <- readIORef pc
      vsp' <- readIORef vsp
      putStrLn $ concat ["pc:", show pc', " vsp:", show vsp', " ", show instruction]
    -}

    action <- case instruction of
      Add out left right -> binary (+) out left right >> proceed
      Call offset depth result -> do
        pc' <- readIORef pc
        enter $ StackFrame pc' depth result
        jump offset
      Equals out left right -> binary (bool .: (==)) out left right >> proceed
      Jump offset -> jump offset
      JumpIfZero register offset -> do
        value <- readRegister register
        if value == 0 then jump offset else proceed
      LessThan out left right -> binary (bool .: (<)) out left right >> proceed
      Move out in_ -> unary id out in_ >> proceed
      Multiply out left right -> binary (*) out left right >> proceed
      Negate out in_ -> unary negate out in_ >> proceed
      Not out in_ -> unary (bool . (== 0)) out in_ >> proceed
      Return result -> do
        csp' <- pred <$> readIORef csp
        result' <- readRegister result
        if csp' < 0 then halt result' else do
          StackFrame pc' _ out <- leave
          writeRegister out result'
          writeIORef pc pc'
          proceed
      Set register (Constant constant) -> writeRegister register constant >> proceed

    case action of
      Proceed -> modifyIORef' pc succ >> loop
      Resume -> loop
      Halt value -> return value

  where
  callStackSize = (2::Int) ^ (12::Int)
  valueStackSize = (2::Int) ^ (20::Int)
  (.:) = (.) . (.)

data Action
  = Proceed
  | Resume
  | Halt !Cell

data StackFrame = StackFrame Int Depth Register

bug :: String -> a
bug = error
