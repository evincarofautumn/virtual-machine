{-#
  LANGUAGE OverloadedStrings
  , BangPatterns
  , GADTs
  , GeneralizedNewtypeDeriving
  , LambdaCase
  , NoMonomorphismRestriction
  , RecordWildCards
  , ViewPatterns
  #-}

module Main where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
import Control.Exception hiding (try)
import Data.Function
import Data.IORef
import Data.Int
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.List
import Data.Vector (Vector)
import System.Environment
import System.Exit
import System.IO
import System.IO.Error
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Text.Lazy ()

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as Mutable
import qualified Data.Vector.Unboxed.Mutable as Unboxed

import Debug.Trace

--------------------------------------------------------------------------------
-- Entry point

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> bug "System.IndexOutOfRangeException: Array index is out of range."
    filename : rawMachineArgs -> do
      file <- Lazy.readFile filename `catch` missing
      case parseProgram filename file of
        Left message -> hPrint stderr message >> exitFailure
        Right inputProgram -> do
          let
            (_, program) = runSimpleUniqueMonad
              $ programFromInputProgram inputProgram
          print program
          result <- run inputProgram $ Vector.fromList (map read rawMachineArgs)
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
  | Call Target Depth Register Target
  | Equals Register Register Register
  | Jump Target
  | JumpIfZero Register Target Target
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
  deriving (Enum, Show)

-- | A register name.
newtype Register = Register Int
  deriving (Show)

newtype InputProgram = InputProgram { inputInstructions :: Vector InputInstruction }
  deriving (Show)

type Cell = Int64

parseProgram :: SourceName -> Lazy.Text -> Either ParseError InputProgram
parseProgram = parse program
  where
  program = InputProgram . Vector.fromList <$> (statement `sepEndBy` many1 newline)
  statement = horizontals *> target >>= instruction
  instruction pc = choice
    [ Add <$ (word "Add") <*> registerComma <*> registerComma <*> register
    , Call <$ (word "Call") <*> (target <* comma) <*> (depth <* comma) <*> register <*> next
    , register3 (word "Equals") Equals
    , try $ Jump <$ word "Jump" <*> target
    , JumpIfZero <$ (word "JumpIfZero") <*> registerComma <*> target <*> next
    , register3 (word "LessThan") LessThan
    , try $ register2 (word "Move") Move
    , register3 (word "Multiply") Multiply
    , try $ register2 (word "Negate") Negate
    , register2 (word "Not") Not
    , Return <$ word "Return" <*> register
    , Set <$ word "Set" <*> registerComma <*> constant
    ]
    where next = pure $ succ pc
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
      Unboxed.write vs vsp' value
      modifyIORef' vsp succ
    pushCall value = do
      csp' <- readIORef csp
      Mutable.write cs csp' value
      modifyIORef' csp succ
    binary f out left right = do
      value <- f <$> readRegister left <*> readRegister right
      writeRegister out value
    unary f out in_ = writeRegister out . f =<< readRegister in_
    writeRegister (Register n) x
      = registerOffset n >>= \n' -> Unboxed.write vs n' x
    readRegister (Register n) = Unboxed.read vs =<< registerOffset n
    registerOffset n = (+) <$> readIORef vsp <*> pure n
    jump (Target target) = writeIORef pc target >> return Resume
    proceed = return Proceed
    halt = return . Halt
    enter frame@(StackFrame _ (Depth depth) _) = do
      pushCall frame
      modifyIORef' vsp (+ depth)

    -- Invariant: call stack is not empty.
    leave = do
      frame@(StackFrame _ (Depth depth) _) <- Mutable.read cs . pred =<< readIORef csp
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
      putStr "vsp:"
      print =<< readIORef vsp
      putStr " pc:"
      print =<< readIORef pc
      print instruction
    -}

    action <- case instruction of
      Add out left right -> binary (+) out left right >> proceed
      Call target depth result next -> do
        enter $ StackFrame next depth result
        jump target
      Equals out left right -> binary (bool .: (==)) out left right >> proceed
      Jump target -> jump target
      JumpIfZero register target next -> do
        value <- readRegister register
        if value == 0 then jump target else jump next
      LessThan out left right -> binary (bool .: (<)) out left right >> proceed
      Move out in_ -> unary id out in_ >> proceed
      Multiply out left right -> binary (*) out left right >> proceed
      Negate out in_ -> unary negate out in_ >> proceed
      Not out in_ -> unary (bool . (== 0)) out in_ >> proceed
      Return result -> do
        csp' <- pred <$> readIORef csp
        result' <- readRegister result
        if csp' < 0 then halt result' else do
          StackFrame next _ out <- leave
          writeRegister out result'
          jump next
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

data StackFrame = StackFrame Target Depth Register

--------------------------------------------------------------------------------
-- Optimization

data Indexed a = Indexed { indexOf :: !Int, indexValue :: !a }
  deriving (Show)

programFromInputProgram (InputProgram (Vector.toList -> instructions))
  = runIdMap $ mapM toBlock basicBlocks
  where
  toBlock (Indexed index instructions) = let
    blockInitial = Target index
    (map toMedial -> blockMedials, toFinal -> blockFinal) = initLast instructions
    in return BasicBlock{..}
  toMedial = \case
    Add out left right -> MAdd out left right
    Equals out left right -> MEquals out left right
    LessThan out left right -> MLessThan out left right
    Move out in_ -> MMove out in_
    Multiply out left right -> MMultiply out left right
    Negate out in_ -> MNegate out in_
    Not out in_ -> MNot out in_
    Set register constant -> MSet register constant
    instruction -> error $ "Non-medial instruction in medial position: " ++ show instruction
  toFinal = \case
    Call target depth register next -> FCall target depth register next
    Jump target -> FJump target
    JumpIfZero register target next -> FJumpIfZero register target next
    Return register -> FReturn register
    instruction -> error $ "Non-final instruction in final position: " ++ show instruction

  basicBlocks = (\x -> traceShow x x) . map indexedGroup
    $ groupBy ((==) `on` nearestLabelTo . indexOf) instructionsWithIndices

  -- 'head' is safe here because 'groupBy' produces a list of nonempty lists.
  indexedGroup x = Indexed (head (map indexOf x)) (map indexValue x)

  nearestLabelTo = (`IntSet.lookupLE` labels)
  !labels = (\x -> traceShow x x) . IntSet.insert entryTarget . IntSet.fromList
    $ concatMap instructionLabel instructionsWithIndices
    where
    entryTarget = 0
    instructionLabel (Indexed index instruction) = case instruction of
      Call (Target target) _ _ (Target next) -> [target, next]
      Jump (Target target) -> [target, succ index]
      JumpIfZero _ (Target target) (Target next) -> [target, next]
      Return{} -> [succ index]
      _ -> []

  instructionsWithIndices = zipWith Indexed [0..] instructions

data Program = Program [BasicBlock]

data BasicBlock = BasicBlock
  { blockInitial :: Target
  , blockMedials :: [Medial]
  , blockFinal :: Final
  } deriving (Show)

data Medial
  = MAdd Register Register Register
  | MEquals Register Register Register
  | MLessThan Register Register Register
  | MMove Register Register
  | MMultiply Register Register Register
  | MNegate Register Register
  | MNot Register Register
  | MSet Register Constant
  deriving (Show)

data Final
  = FCall Target Depth Register Target
  | FJump Target
  | FJumpIfZero Register Target Target
  | FReturn Register
  deriving (Show)

isFinal :: InputInstruction -> Bool
isFinal = \case
  Call{} -> True
  Jump{} -> True
  JumpIfZero{} -> True
  Return{} -> True
  _ -> False

{-
-- | An instruction in the intermediate representation, indexed by openness at
-- entry and exit: an instruction with a closed entry cannot be preceded by
-- another instruction, and an instruction with a closed exit cannot itself
-- precede another instruction. A basic block comprises a list of instructions,
-- closed at both ends.
data Instruction e x where
  ILabel :: Label -> Instruction C O
  IAdd :: Register -> Register -> Register -> Instruction O O
  ICall :: Label -> Depth -> Register -> Instruction O C
  IEquals :: Register -> Register -> Register -> Instruction O O
  IJump :: Label -> Instruction O C
  IJumpIfZero :: Register -> Label -> Label -> Instruction O C
  ILessThan :: Register -> Register -> Register -> Instruction O O
  IMove :: Register -> Register -> Instruction O O
  IMultiply :: Register -> Register -> Register -> Instruction O O
  INegate :: Register -> Register -> Instruction O O
  INot :: Register -> Register -> Instruction O O
  IReturn :: Register -> Instruction O C
  ISet :: Register -> Constant -> Instruction O O

data IrProgram = IrProgram
  { programEntry :: Label
  , programBody :: Graph Instruction C C
  }
-}

--------------------------------------------------------------------------------
-- Miscellany

bug :: String -> a
bug = error

initLast :: [a] -> ([a], a)
initLast [] = error "initLast: empty list"
initLast [x] = ([], x)
initLast (x:xs) = let (xs', x') = initLast xs in (x : xs', x')

--------------------------------------------------------------------------------
-- Source of unique labels

type IdMap = IntMap Label

newtype IdMapMonad a = IdMapMonad
  { unIdMap :: IdMap -> SimpleUniqueMonad (IdMap, a) }

instance Monad IdMapMonad where
  return x = IdMapMonad $ \env -> return (env, x)
  IdMapMonad f >>= m = IdMapMonad $ \env -> do
    (env', x) <- f env
    unIdMap (m x) env'

freshId index = IdMapMonad $ \env -> case IntMap.lookup index env of
  Just existing -> return (env, existing)
  Nothing -> do
    label <- freshLabel
    return (IntMap.insert index label env, label)

runIdMap (IdMapMonad m) = m IntMap.empty
