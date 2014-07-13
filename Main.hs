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
  , StandaloneDeriving
  , TypeFamilies
  , ViewPatterns
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
import Control.Exception hiding (try)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Function
import Data.IORef
import Data.Int
import Data.IntMap (IntMap)
import Data.List
import Data.Map (Map)
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import Data.Vector (Vector)
import System.Environment
-- import System.Exit
-- import System.IO
import System.IO.Error
import Text.Parsec hiding (State, (<|>), label, labels, many)
import Text.Parsec.Text.Lazy ()

import qualified Compiler.Hoopl as Hoopl
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
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
      (optimized, entry) <- return . runSimpleUniqueMonad $ do
        parsed <- parseProgram filename file
        case parsed of
          (_, Left message) -> error $ show message  -- hPrint stderr message >> exitFailure
          (_idMap, Right inputProgram) -> do
            (program, entry) <- programFromInputProgram inputProgram
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

--------------------------------------------------------------------------------
-- Input data types

-- | An instruction in the input program.
data InputInstruction
  = Add !Register !Register !Register
  | Call {-lazy-}(Labelled Target) !Depth !Register {-lazy-}(Labelled Target)
  | Equals !Register !Register !Register
  | Jump {-lazy-}(Labelled Target)
  | JumpIfZero !Register {-lazy-}(Labelled Target) {-lazy-}(Labelled Target)
  | LessThan !Register !Register !Register
  | Move !Register !Register
  | Multiply !Register !Register !Register
  | Negate !Register !Register
  | Not !Register !Register
  | Return !Register
  | Set !Register !Constant
  deriving (Show)

inputSuccessors :: InputInstruction -> Set Label
inputSuccessors = \case
  Call (Labelled l _) _ _ (Labelled n _) -> Set.fromList [l, n]
  Jump (Labelled l _) -> Set.singleton l
  JumpIfZero _ (Labelled t _) (Labelled f _) -> Set.fromList [t, f]
  Return{} -> Set.empty
  _ -> Set.empty

data Labelled a = Labelled { labelledLabel :: !Label, labelledValue :: !a }
  deriving (Eq, Ord, Show)

-- | A constant integer in the input program.
newtype Constant = Constant Cell

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

newtype InputProgram = InputProgram
  { inputInstructions :: Vector (Labelled InputInstruction) }
  deriving (Show)

type Cell = Int64

parseProgram
  :: SourceName
  -> Lazy.Text
  -> SimpleUniqueMonad (IdMap, Either ParseError InputProgram)
parseProgram filename file = runIdMap
  $ runParserT program () filename file
  where
  program = InputProgram . Vector.fromList -- . concat
    <$> ((statement `sepEndBy` many1 newline) <* eof)
  statement = horizontals *> target >>= instruction
  instruction pc = do
    current <- lift $ labelForTarget pc
    next <- let pc' = succ pc
      in Labelled <$> lift (labelForTarget pc') <*> pure pc'
    Labelled current <$> (medial <|> final next)
    where
    medial = choice
      [ Add <$ word "Add" <*> registerComma <*> registerComma <*> register
      , register3 (word "Equals") Equals
      , register3 (word "LessThan") LessThan
      , try $ register2 (word "Move") Move
      , register3 (word "Multiply") Multiply
      , try $ register2 (word "Negate") Negate
      , register2 (word "Not") Not
      , Set <$ word "Set" <*> registerComma <*> constant
      ]
    final next = choice
      [ Call <$ word "Call"
        <*> (label <* comma) <*> (depth <* comma) <*> register <*> pure next
      , try $ Jump <$ word "Jump" <*> label
      , JumpIfZero <$ word "JumpIfZero"
        <*> registerComma <*> label <*> pure next
      , Return <$ word "Return" <*> register
      ]
    label = do
      t <- target
      Labelled <$> lift (labelForTarget t) <*> pure t
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

run :: Label -> Graph Instruction C C -> Vector Cell -> IO Cell
run entry graph machineArguments = do
  let (Target entry', instructions) = flatten entry graph
  putStrLn "Flattened:"
  mapM_ (\ (l, i) -> do putStr (show l ++ ": "); print i)
    . zip [(0::Int)..] $ Vector.toList instructions

  cs <- Mutable.new callStackSize
  vs <- Unboxed.new valueStackSize
  csp <- newIORef (0 :: Int)
  vsp <- newIORef (0 :: Int)
  pc <- newIORef entry'

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

    action <- case instruction of
      Add out left right -> binary (+) out left right >> proceed
      Call (Labelled _ target) depth result (Labelled _ next) -> do
        enter $ StackFrame next depth result
        jump target
      Equals out left right -> binary (bool .: (==)) out left right >> proceed
      Jump (Labelled _ target) -> jump target
      JumpIfZero register (Labelled _ target) (Labelled _ next) -> do
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

data Action
  = Proceed
  | Resume
  | Halt !Cell

data StackFrame = StackFrame Target Depth Register

--------------------------------------------------------------------------------
-- Optimization

data Indexed a = Indexed { indexOf :: !Int, indexValue :: !a }
  deriving (Show)

programFromInputProgram
  :: InputProgram
  -> SimpleUniqueMonad (Graph Instruction C C, Label)
programFromInputProgram (InputProgram (Vector.toList -> instructions)) = do
  blockified <- flip evalStateT usedLabels $ blockify instructions
  return
    ( foldl' (|*><*|) emptyClosedGraph blockified
    , labelledLabel $ head instructions
    )
  where
  usedLabels = mconcatMap (inputSuccessors . labelledValue) instructions

  blockify
    :: [Labelled InputInstruction]
    -> StateT (Set Label) SimpleUniqueMonad [Graph Instruction C C]
  blockify is@(i : _) = do
    (medials, is') <- spanJustM toMedial is
    let (mFinal, is'') = spanJust1 toFinal is'
    (initial, final, is''') <- case mFinal of
      Just explicitFinal -> do
        implicitLabel <- liftM ILabel freshLabel
        return (implicitLabel, explicitFinal, is'')
      Nothing -> case is'' of
        next : rest -> return
          (ILabel $ labelledLabel i, IJump $ labelledLabel next, next : rest)
        [] -> error "Missing final instruction in basic block."
    liftM ((mkFirst initial Hoopl.<*> mkMiddles medials Hoopl.<*> mkLast final) :)
      $ blockify is'''
  blockify [] = return []

  toMedial (Labelled label instruction)
    = gets (Set.member label) >>= \used -> if used
      then modify (Set.delete label) >> return Nothing
      else return $ case instruction of
        Add out left right -> Just $ IAdd out left right
        Equals out left right -> Just $ IEquals out left right
        LessThan out left right -> Just $ ILessThan out left right
        Move out in_ -> Just $ IMove out in_
        Multiply out left right -> Just $ IMultiply out left right
        Negate out in_ -> Just $ INegate out in_
        Not out in_ -> Just $ INot out in_
        Set register constant -> Just $ ISet register constant
        _ -> Nothing

  toFinal (Labelled _ instruction) = case instruction of
    Call (Labelled target _) depth register (Labelled next _)
      -> Just $ ICall target depth register next
    Jump (Labelled target _) -> Just $ IJump target
    JumpIfZero register (Labelled target _) (Labelled next _)
      -> Just $ IJumpIfZero register target next
    Return register -> Just $ IReturn register
    _ -> Nothing

-- | An instruction in the intermediate representation, indexed by openness at
-- entry and exit: an instruction with a closed entry cannot be preceded by
-- another instruction, and an instruction with a closed exit cannot itself
-- precede another instruction. A basic block comprises a list of instructions,
-- closed at both ends.
data Instruction e x where
  ILabel :: Label -> Instruction C O
  IAdd :: Register -> Register -> Register -> Instruction O O
  ICall :: Label -> Depth -> Register -> Label -> Instruction O C
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

instance Show (Instruction e x) where
  show = \case
    ILabel label -> show label ++ ":"
    IAdd a b c -> '\t' : unwords [show a, ":=", show b, "+", show c]
    ICall a _ b next -> '\t' : unwords [show b, ":= call", show a, "then", show next]
    IEquals a b c -> '\t' : unwords [show a, ":=", show b, "=", show c]
    IJump label -> '\t' : unwords ["jump", show label]
    IJumpIfZero a t f -> '\t' : unwords ["if", show a, "= 0 then", show t, "else", show f]
    ILessThan a b c -> '\t' : unwords [show a, ":=", show b, "<", show c]
    IMove a b -> '\t' : unwords [show a, ":=", show b]
    IMultiply a b c -> '\t' : unwords [show a, ":=", show b, "*", show c]
    INegate a b -> '\t' : unwords [show a, ":= -", show b]
    INot a b -> '\t' : unwords [show a, ":= not", show b]
    IReturn a -> '\t' : unwords ["ret", show a]
    ISet a b -> '\t' : unwords [show a, ":=", show b]

instance NonLocal Instruction where
  entryLabel (ILabel l) = l
  successors = \case
    ICall l _ _ n -> [l, n]
    IJump l -> [l]
    IJumpIfZero _ t f -> [t, f]
    IReturn{} -> []

instructionRegisters :: Instruction e x -> Set Register
instructionRegisters = \case
  ILabel{} -> Set.empty
  IAdd a b c -> Set.fromList [a, b, c]
  ICall _ _ a _ -> Set.singleton a
  IEquals a b c -> Set.fromList [a, b, c]
  IJump _ -> Set.empty
  IJumpIfZero a _ _ -> Set.singleton a
  ILessThan a b c -> Set.fromList [a, b, c]
  IMove a b -> Set.fromList [a, b]
  IMultiply a b c -> Set.fromList [a, b, c]
  INegate a b -> Set.fromList [a, b]
  INot a b -> Set.fromList [a, b]
  IReturn a -> Set.singleton a
  ISet a _ -> Set.singleton a

optimize
  :: Label
  -> Graph Instruction C C
  -> SimpleUniqueMonad (Graph Instruction C C)
optimize entry program = runWithFuel infiniteFuel rewrite
  where
  rewrite :: SimpleFuelMonad (Graph Instruction C C)
  rewrite = do
    (rewritten, _, _) <- analyzeAndRewriteBwd livenessPass (JustC entry) program noFacts
    return rewritten

  livenessPass :: (FuelMonad m) => BwdPass m Instruction (Set Register)
  livenessPass = BwdPass
    { bp_lattice = livenessLattice
    , bp_transfer = livenessTransfer
    , bp_rewrite = livenessRewrite
    }

  livenessTransfer :: BwdTransfer Instruction (Set Register)
  livenessTransfer = mkBTransfer3
    livenessAnalysisInitial
    livenessAnalysisMedial
    livenessAnalysisFinal

  livenessAnalysisInitial :: Instruction C O -> Set Register -> Set Register
  livenessAnalysisInitial ILabel{} facts = facts

  -- A register is not alive before an assignment, so target registers are
  -- always omitted from the fact base before proceeding.
  livenessAnalysisMedial :: Instruction O O -> Set Register -> Set Register
  livenessAnalysisMedial instruction facts = case instruction of
    IAdd out _ _ -> addUsesBut out
    IEquals out _ _ -> addUsesBut out
    ILessThan out _ _ -> addUsesBut out
    IMove out _ -> addUsesBut out
    IMultiply out _ _ -> addUsesBut out
    INegate out _ -> addUsesBut out
    INot out _ -> addUsesBut out
    ISet out _ -> addUsesBut out
    where addUsesBut x = addUses (Set.delete x facts) instruction

  livenessAnalysisFinal :: Instruction O C -> FactBase (Set Register) -> (Set Register)
  livenessAnalysisFinal instruction facts = case instruction of
    IJump label -> addUses (fact facts label) instruction
    IJumpIfZero _ true false
      -> addUses (fact facts true <> fact facts false) instruction
    ICall _ _ out label -> addUses (Set.delete out (fact facts label)) instruction
    IReturn _ -> addUses (fact_bot livenessLattice) instruction

  livenessLattice = DataflowLattice
    { fact_name = "live registers"
    , fact_bot = Set.empty
    , fact_join = \_ (OldFact old) (NewFact new) -> let
      factChange = changeIf (Set.size factJoin > Set.size old)
      factJoin = old <> new
      in (factChange, factJoin)
    }

  livenessRewrite :: (FuelMonad m) => BwdRewrite m Instruction (Set Register)
  livenessRewrite = mkBRewrite3
    livenessRewriteInitial
    livenessRewriteMedial
    livenessRewriteFinal

  livenessRewriteInitial :: (FuelMonad m) => n C O -> f -> m (Maybe (Graph n C O))
  livenessRewriteInitial _node _facts = return Nothing

  livenessRewriteMedial :: (FuelMonad m) => n O O -> f -> m (Maybe (Graph n O O))
  livenessRewriteMedial _node _facts = return Nothing

  livenessRewriteFinal :: (FuelMonad m) => n O C -> FactBase f -> m (Maybe (Graph n O C))
  livenessRewriteFinal _node _facts = return Nothing

  fact :: FactBase (Set a) -> Label -> Set a
  fact facts label = fromMaybe Set.empty $ lookupFact label facts

  addUses :: Set Register -> Instruction e x -> Set Register
  addUses to = (<> to) . instructionRegisters

--------------------------------------------------------------------------------
-- Flattening graphs back into executable instructions

flatten :: Label -> Graph Instruction C C -> (Target, Vector InputInstruction)
flatten entry graph =
  ( labelledValue $ targetForLabel entry
  , Vector.reverse $ Vector.fromList finalInstructions
  )
  where
  (finalLabels, finalInstructions)
    = foldGraphNodes addNode graph (Map.empty, [])

  targetForLabel :: Label -> Labelled Target
  targetForLabel label = Labelled label $ Target
    $ case Map.lookup label finalLabels of
      Nothing -> error $ unwords ["Missing target for label", show label]
      Just target -> target

  addNode
    :: Instruction e x
    -> (Map Label Int, [InputInstruction])
    -> (Map Label Int, [InputInstruction])
  addNode i (labels, is) = case i of
    ILabel label -> (Map.insert label (length is) labels, is)
    IAdd out left right -> instruction $ Add out left right
    ICall target depth out next -> instruction
      $ Call (targetForLabel target) depth out (targetForLabel next)
    IEquals out left right -> instruction $ Equals out left right
    IJump target -> instruction $ Jump (targetForLabel target)
    IJumpIfZero register true false -> instruction
      $ JumpIfZero register (targetForLabel true) (targetForLabel false)
    ILessThan out left right -> instruction $ LessThan out left right
    IMove out in_ -> instruction $ Move out in_
    IMultiply out left right -> instruction $ Multiply out left right
    INegate out in_ -> instruction $ Negate out in_
    INot out in_ -> instruction $ Not out in_
    IReturn register -> instruction $ Return register
    ISet register value -> instruction $ Set register value
    where
    instruction x = (labels, x : is)

--------------------------------------------------------------------------------
-- Miscellany

bug :: String -> a
bug = error

mconcatMap :: (Monoid b) => (a -> b) -> [a] -> b
mconcatMap = mconcat .: map

spanJustM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m ([b], [a])
spanJustM f = go []
  where
  -- These 'reverse's could be gotten rid of with a bit more cleverness.
  go ys l = case l of
    x : xs -> do
      my <- f x
      case my of
        Just y -> go (y : ys) xs
        Nothing -> return (reverse ys, l)
    [] -> return (reverse ys, l)

spanJust1 :: (a -> Maybe b) -> [a] -> (Maybe b, [a])
spanJust1 f l@(x : xs) = case f x of
  Nothing -> (Nothing, l)
  x'@Just{} -> (x', xs)
spanJust1 _ [] = (Nothing, [])

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)

instance (UniqueMonad m) => UniqueMonad (StateT s m) where
  freshUnique = lift freshUnique

--------------------------------------------------------------------------------
-- Source of unique labels

type IdMap = IntMap Label

invertIdMap :: IdMap -> Map Label Int
invertIdMap = Map.fromList . map swap . IntMap.toList
  where swap (a, b) = (b, a)

newtype IdMapMonad a = IdMapMonad
  { unIdMap :: IdMap -> SimpleUniqueMonad (IdMap, a) }

instance Monad IdMapMonad where
  return x = IdMapMonad $ \env -> return (env, x)
  IdMapMonad f >>= m = IdMapMonad $ \env -> do
    (env', x) <- f env
    unIdMap (m x) env'

instance Functor IdMapMonad where
  fmap f m = m >>= return . f

instance Applicative IdMapMonad where
  pure x = IdMapMonad $ \env -> return (env, x)
  mf <*> mx = do
    f <- mf
    x <- mx
    return $ f x

labelForTarget :: Target -> IdMapMonad Label
labelForTarget (Target index) = IdMapMonad
  $ \env -> case IntMap.lookup index env of
    Just existing -> return (env, existing)
    Nothing -> do
      label <- freshLabel
      return (IntMap.insert index label env, label)

runIdMap :: IdMapMonad a -> SimpleUniqueMonad (IdMap, a)
runIdMap (IdMapMonad m) = m IntMap.empty
