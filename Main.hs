{-#
  LANGUAGE OverloadedStrings
  , TypeSynonymInstances
  , FlexibleContexts
  , FlexibleInstances
  , NoMonomorphismRestriction
  #-}

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
import qualified Data.Vector.Unboxed.Mutable as Unboxed

--------------------------------------------------------------------------------
-- Entry point

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> bug "System.IndexOutOfRangeException: Array index is out of range."
    filename : rawMachineArgs -> do
      file <- Lazy.readFile filename `catch` missing
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

--------------------------------------------------------------------------------
-- Input data types

-- | An instruction in the input program.
data InputInstruction
  = Add Register Register Register
  | Call Target Depth Register
  | Equals Register Register Register
  | Jump Target
  | JumpIfZero Register Target
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

-- | A jump target in the input program.
newtype Target = Target Int
  deriving (Show)

-- | A register name.
newtype Register = Register Int
  deriving (Show)

newtype InputProgram = InputProgram (Vector InputInstruction)
  deriving (Show)

type Cell = Int64

readProgram :: SourceName -> Lazy.Text -> Either ParseError InputProgram
readProgram = parse program
  where
  program = InputProgram . Vector.fromList <$> (statement `sepEndBy` many1 newline)
  statement = horizontals *> digits *> instruction
  instruction = choice
    [ Add <$ (word "Add") <*> registerComma <*> registerComma <*> register
    , Call <$ (word "Call") <*> (target <* comma) <*> (depth <* comma) <*> register
    , register3 (word "Equals") Equals
    , try $ Jump <$ word "Jump" <*> target
    , JumpIfZero <$ (word "JumpIfZero") <*> registerComma <*> target
    , register3 (word "LessThan") LessThan
    , try $ register2 (word "Move") Move
    , register3 (word "Multiply") Multiply
    , try $ register2 (word "Negate") Negate
    , register2 (word "Not") Not
    , Return <$ word "Return" <*> register
    , Set <$ word "Set" <*> registerComma <*> constant
    ]
  digits = lexeme (many1 digit) <?> "number"
  target = Target <$> unsigned <?> "jump target"
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
  vs <- Unboxed.new valueStackSize
  csp <- newIORef (0 :: Int)
  vsp <- newIORef (0 :: Int)
  pc <- newIORef (0 :: Int)

  let
    pushValue value = do
      vsp' <- readIORef vsp
      Unboxed.unsafeWrite vs vsp' value
      modifyIORef' vsp succ
    pushCall value = do
      csp' <- readIORef csp
      Mutable.unsafeWrite cs csp' value
      modifyIORef' csp succ
    binary f out left right = do
      value <- f <$> readRegister left <*> readRegister right
      writeRegister out value
    unary f out in_ = writeRegister out . f =<< readRegister in_
    writeRegister (Register n) x
      = registerOffset n >>= \n' -> Unboxed.unsafeWrite vs n' x
    readRegister (Register n) = Unboxed.unsafeRead vs =<< registerOffset n
    registerOffset n = (+) <$> readIORef vsp <*> pure n
    jump (Target target) = writeIORef pc target >> return Resume
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

    action <- case instruction of
      Add out left right -> binary (+) out left right >> proceed
      Call target depth result -> do
        pc' <- readIORef pc
        enter $ StackFrame pc' depth result
        jump target
      Equals out left right -> binary (bool .: (==)) out left right >> proceed
      Jump target -> jump target
      JumpIfZero register target -> do
        value <- readRegister register
        if value == 0 then jump target else proceed
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
