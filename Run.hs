{-#
  LANGUAGE BangPatterns
  , DataKinds
  , GADTs
  #-}

module Run
  ( run
  ) where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
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

run :: Label -> Graph Node C C -> Vector Cell -> IO Cell
run entry graph machineArguments = do
  let (Target entry', !instructions0) = flatten entry graph
  -- We don't actually need to mutate the instruction vector, but thawing allows
  -- us to use unchecked reads, which saves a bounds check per instruction.
  !instructions <- Vector.thaw instructions0

  cs <- Unboxed.new callStackSize  -- Call stack
  vs <- Unboxed.new valueStackSize  -- Value stack
  csp <- newIORef (0 :: Int)  -- Call stack pointer
  vsp <- newIORef (0 :: Int)  -- Value stack pointer
  pc <- newIORef entry'  -- Program counter

  let

    {-# INLINE pushValue #-}
    pushValue value = do
      vsp' <- readIORef vsp
      Unboxed.unsafeWrite vs vsp' value
      modifyIORef' vsp succ

    {-# INLINE pushCall #-}
    pushCall value = do
      csp' <- readIORef csp
      Unboxed.unsafeWrite cs csp' value
      modifyIORef' csp succ

    {-# INLINE binary #-}
    binary f out left right = do
      value <- f <$> readRegister left <*> readRegister right
      writeRegister out value

    {-# INLINE inPlaceBinary #-}
    inPlaceBinary f out right = do
      value <- f <$> readRegister out <*> readRegister right
      writeRegister out value

    {-# INLINE unary #-}
    unary f out in_ = writeRegister out . f =<< readRegister in_

    {-# INLINE inPlaceUnary #-}
    inPlaceUnary f out = writeRegister out . f =<< readRegister out

    {-# INLINE writeRegister #-}
    writeRegister (Register n) x
      = registerOffset n >>= \n' -> Unboxed.unsafeWrite vs n' x

    {-# INLINE readRegister #-}
    readRegister (Register n) = Unboxed.unsafeRead vs =<< registerOffset n

    {-# INLINE registerOffset #-}
    registerOffset n = (+) <$> readIORef vsp <*> pure n

    {-# INLINE jump #-}
    jump (Target target) = writeIORef pc target >> return Resume

    {-# INLINE proceed #-}
    proceed = return Proceed

    {-# INLINE halt #-}
    halt = return . Halt

    {-# INLINE enter #-}
    enter (Depth depth) target = do
      pushCall =<< readIORef pc
      modifyIORef' vsp (+ depth)
      jump target

    -- Invariant: call stack is not empty.
    {-# INLINE leave #-}
    leave result = do
      target <- Unboxed.unsafeRead cs . pred =<< readIORef csp
      -- We reload the call instruction so that we only have to store the return
      -- address on the call stack, not the output register or next address.
      ICall _ (Depth depth) out (Labelled _ next)
        <- Mutable.unsafeRead instructions target
      modifyIORef' vsp (subtract depth)
      modifyIORef' csp pred
      writeRegister out result
      jump next

    {-# INLINE bool #-}
    bool :: Bool -> Cell
    bool x = if x then 1 else 0

  Vector.mapM_ pushValue machineArguments

  let
    loop = do
      instruction <- Mutable.unsafeRead instructions =<< readIORef pc

      action <- case instruction of
        IAddRR out left right -> {-# SCC "IAddRR" #-} binary (+) out left right >> proceed
        IAddRC out left (Constant right) -> {-# SCC "IAddRC" #-} unary (+ right) out left >> proceed
        IAddR out in_ -> {-# SCC "IAddR" #-} inPlaceBinary (+) out in_ >> proceed
        IAddC out (Constant in_) -> {-# SCC "IAddC" #-} inPlaceUnary (+ in_) out >> proceed
        ICall (Labelled _ target) depth _ _ -> {-# SCC "ICall" #-} enter depth target
        IEqualsRR out left right -> {-# SCC "IEqualsRR" #-} binary (bool .: (==)) out left right >> proceed
        IEqualsRC out left (Constant right) -> {-# SCC "IEqualsRC" #-} unary (bool . (== right)) out left >> proceed
        IEqualsR out in_ -> {-# SCC "IEqualsR" #-} inPlaceBinary (bool .: (==)) out in_ >> proceed
        IEqualsC out (Constant in_) -> {-# SCC "IEqualsC" #-} inPlaceUnary (bool . (== in_)) out >> proceed
        IJump (Labelled _ target) -> {-# SCC "IJump" #-} jump target
        IJumpIfZero register (Labelled _ target) (Labelled _ next) -> {-# SCC "IJumpIfZero" #-} do
          value <- readRegister register
          if value == 0 then jump target else jump next
        ILessThanRR out left right -> {-# SCC "ILessThanRR" #-} binary (bool .: (<)) out left right >> proceed
        ILessThanRC out left (Constant right) -> {-# SCC "ILessThanRC" #-} unary (bool . (< right)) out left >> proceed
        ILessThanR out in_ -> {-# SCC "ILessThanR" #-} inPlaceBinary (bool .: (<)) out in_ >> proceed
        ILessThanC out (Constant in_) -> {-# SCC "ILessThanC" #-} inPlaceUnary (bool . (< in_)) out >> proceed
        IMultiplyRR out left right -> {-# SCC "IMultiplyRR" #-} binary (*) out left right >> proceed
        IMultiplyRC out left (Constant right) -> {-# SCC "IMultiplyRC" #-} unary (* right) out left >> proceed
        IMultiplyR out in_ -> {-# SCC "IMultiplyR" #-} inPlaceBinary (*) out in_ >> proceed
        IMultiplyC out (Constant in_) -> {-# SCC "IMultiplyC" #-} inPlaceUnary (* in_) out >> proceed
        INegateR out in_ -> {-# SCC "INegateR" #-} unary negate out in_ >> proceed
        INegate out -> {-# SCC "INegate" #-} inPlaceUnary negate out >> proceed
        INotR out in_ -> {-# SCC "INotR" #-} unary (bool . (== 0)) out in_ >> proceed
        INot out -> {-# SCC "INot" #-} inPlaceUnary (bool . (== 0)) out >> proceed
        IReturn result -> {-# SCC "IReturn" #-} do
          csp' <- pred <$> readIORef csp
          result' <- readRegister result
          if csp' < 0 then halt result' else leave result'
        ISetRR out in_ -> {-# SCC "ISetRR" #-} unary id out in_ >> proceed
        ISetRC register (Constant constant)
          -> {-# SCC "ISetRC" #-} writeRegister register constant >> proceed

      case action of
        Proceed -> modifyIORef' pc succ >> loop
        Resume -> loop
        Halt value -> return value
    in loop

  where
  callStackSize = (2::Int) ^ (12::Int)
  valueStackSize = (2::Int) ^ (20::Int)

-- | Flattens a control flow graph into executable instructions.
flatten :: Label -> Graph Node C C -> (Target, Vector (Instruction Optimized))
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
    -> (Map Label Int, [Instruction Optimized])
    -> (Map Label Int, [Instruction Optimized])
  addNode i (labels, is) = case i of
    NLabel label -> (Map.insert label (length is) labels, is)
    NAdd out left right -> instruction $ if out == left
      then operand (IAddR out) (IAddC out) right
      else operand (IAddRR out left) (IAddRC out left) right
    NCall target depth out next -> instruction
      $ ICall (targetForLabel target) depth out (targetForLabel next)
    NEquals out left right -> instruction $ if out == left
      then operand (IEqualsR out) (IEqualsC out) right
      else operand (IEqualsRR out left) (IEqualsRC out left) right
    NJump target -> instruction $ IJump (targetForLabel target)
    NJumpIfZero register true false -> instruction
      $ IJumpIfZero register (targetForLabel true) (targetForLabel false)
    NLessThan out left right -> instruction $ if out == left
      then operand (ILessThanR out) (ILessThanC out) right
      else operand (ILessThanRR out left) (ILessThanRC out left) right
    NMultiply out left right -> instruction $ if out == left
      then operand (IMultiplyR out) (IMultiplyC out) right
      else operand (IMultiplyRR out left) (IMultiplyRC out left) right
    NNegate out in_ -> instruction
      $ if out == in_ then INegate out else INegateR out in_
    NNot out in_ -> instruction
      $ if out == in_ then INot out else INotR out in_
    NReturn register -> instruction $ IReturn register
    NSet out in_ -> instruction $ operand (ISetRR out) (ISetRC out) in_
    where instruction x = (labels, x : is)
