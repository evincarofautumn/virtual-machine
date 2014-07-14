{-# LANGUAGE GADTs #-}

module Run
  ( run
  ) where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
import Data.Function
import Data.IORef
import Data.Map (Map)
import Data.Vector (Vector)

import qualified Data.Map as Map
import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as Mutable
import qualified Data.Vector.Unboxed.Mutable as Unboxed

import Instruction
import Node
import Types
import Utils

-- | The action to take at each step of program execution:
--
--  * 'Proceed' to the next instruction.
--
--  * 'Resume' after a jump.
--
--  * 'Halt' with a return value.
--
data Action
  = Proceed
  | Resume
  | Halt !Cell

data StackFrame = StackFrame
  Target  -- ^ Jump target.
  Depth  -- ^ Number of registers to save.
  Register  -- ^ Register in which to save result.

run :: Label -> Graph Node C C -> Vector Cell -> IO Cell
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
      IAdd out left right -> binary (+) out left right >> proceed
      ICall (Labelled _ target) depth result (Labelled _ next) -> do
        enter $ StackFrame next depth result
        jump target
      IEquals out left right -> binary (bool .: (==)) out left right >> proceed
      IJump (Labelled _ target) -> jump target
      IJumpIfZero register (Labelled _ target) (Labelled _ next) -> do
        value <- readRegister register
        if value == 0 then jump target else jump next
      ILessThan out left right -> binary (bool .: (<)) out left right >> proceed
      IMove out in_ -> unary id out in_ >> proceed
      IMultiply out left right -> binary (*) out left right >> proceed
      INegate out in_ -> unary negate out in_ >> proceed
      INot out in_ -> unary (bool . (== 0)) out in_ >> proceed
      IReturn result -> do
        csp' <- pred <$> readIORef csp
        result' <- readRegister result
        if csp' < 0 then halt result' else do
          StackFrame next _ out <- leave
          writeRegister out result'
          jump next
      ISet register (Constant constant)
        -> writeRegister register constant >> proceed

    case action of
      Proceed -> modifyIORef' pc succ >> loop
      Resume -> loop
      Halt value -> return value

  where
  callStackSize = (2::Int) ^ (12::Int)
  valueStackSize = (2::Int) ^ (20::Int)

-- | Flattens a control flow graph into executable instructions.
flatten :: Label -> Graph Node C C -> (Target, Vector Instruction)
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
    :: Node e x
    -> (Map Label Int, [Instruction])
    -> (Map Label Int, [Instruction])
  addNode i (labels, is) = case i of
    NLabel label -> (Map.insert label (length is) labels, is)
    NAdd out left right -> instruction $ IAdd out left right
    NCall target depth out next -> instruction
      $ ICall (targetForLabel target) depth out (targetForLabel next)
    NEquals out left right -> instruction $ IEquals out left right
    NJump target -> instruction $ IJump (targetForLabel target)
    NJumpIfZero register true false -> instruction
      $ IJumpIfZero register (targetForLabel true) (targetForLabel false)
    NLessThan out left right -> instruction $ ILessThan out left right
    NMove out in_ -> instruction $ IMove out in_
    NMultiply out left right -> instruction $ IMultiply out left right
    NNegate out in_ -> instruction $ INegate out in_
    NNot out in_ -> instruction $ INot out in_
    NReturn register -> instruction $ IReturn register
    NSet register value -> instruction $ ISet register value
    where
    instruction x = (labels, x : is)