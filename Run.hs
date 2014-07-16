{-#
  LANGUAGE BangPatterns
  , DataKinds
  , GADTs
  #-}

module Run
  ( run
  ) where

import Control.Applicative
import Data.IORef
import Data.Vector (Vector)

import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as Mutable
import qualified Data.Vector.Unboxed.Mutable as Unboxed

import Instruction
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

-- | Runs a program from the given entry point address with the given machine
-- arguments, and returns its exit code.
run :: Vector (Instruction a) -> Target -> Vector Cell -> IO Cell
run instructions0 (Target entry) machineArguments = do
  -- We don't actually need to mutate the instruction vector, but thawing allows
  -- us to use unchecked reads, which saves a bounds check per instruction.
  !instructions <- Vector.thaw instructions0
  cs <- Unboxed.new callStackSize  -- Call stack
  vs <- Unboxed.new valueStackSize  -- Value stack
  csp <- newIORef (0 :: Int)  -- Call stack pointer
  vsp <- newIORef (0 :: Int)  -- Value stack pointer
  pc <- newIORef entry  -- Program counter

  let
    pushValue :: Cell -> IO ()
    pushValue value = do
      vsp' <- readIORef vsp
      Unboxed.unsafeWrite vs vsp' value
      modifyIORef' vsp succ
    {-# INLINE pushValue #-}

    pushCall :: Int -> IO ()
    pushCall value = do
      csp' <- readIORef csp
      Unboxed.unsafeWrite cs csp' value
      modifyIORef' csp succ
    {-# INLINE pushCall #-}

    binary
      :: (Cell -> Cell -> Cell) -> Register -> Register -> Register -> IO ()
    binary f out left right = do
      value <- f <$> readRegister left <*> readRegister right
      writeRegister out value
    {-# INLINE binary #-}

    inPlaceBinary :: (Cell -> Cell -> Cell) -> Register -> Register -> IO ()
    inPlaceBinary f out right = do
      value <- f <$> readRegister out <*> readRegister right
      writeRegister out value
    {-# INLINE inPlaceBinary #-}

    unary :: (Cell -> Cell) -> Register -> Register -> IO ()
    unary f out in_ = writeRegister out . f =<< readRegister in_
    {-# INLINE unary #-}

    inPlaceUnary :: (Cell -> Cell) -> Register -> IO ()
    inPlaceUnary f out = writeRegister out . f =<< readRegister out
    {-# INLINE inPlaceUnary #-}

    writeRegister :: Register -> Cell -> IO ()
    writeRegister (Register n) x
      = registerOffset n >>= \n' -> Unboxed.unsafeWrite vs n' x
    {-# INLINE writeRegister #-}

    readRegister :: Register -> IO Cell
    readRegister (Register n) = Unboxed.unsafeRead vs =<< registerOffset n
    {-# INLINE readRegister #-}

    registerOffset :: Int -> IO Int
    registerOffset n = (+) <$> readIORef vsp <*> pure n
    {-# INLINE registerOffset #-}

    jump :: Target -> IO Action
    jump (Target target) = writeIORef pc target >> return Resume
    {-# INLINE jump #-}

    proceed :: IO Action
    proceed = return Proceed
    {-# INLINE proceed #-}

    halt :: Cell -> IO Action
    halt = return . Halt
    {-# INLINE halt #-}

    enter :: Depth -> Target -> IO Action
    enter (Depth depth) target = do
      pushCall =<< readIORef pc
      modifyIORef' vsp (+ depth)
      jump target
    {-# INLINE enter #-}

    -- Invariant: call stack is not empty.
    leave :: Cell -> IO Action
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
    {-# INLINE leave #-}

    bool :: Bool -> Cell
    bool x = if x then 1 else 0
    {-# INLINE bool #-}

  Vector.mapM_ pushValue machineArguments

  let
    loop :: IO Cell
    loop = do
      instruction <- Mutable.unsafeRead instructions =<< readIORef pc
      action <- case instruction of
        IAddRR out left right -> {-# SCC "IAddRR" #-}
          binary (+) out left right >> proceed
        IAddRC out left (Constant right) -> {-# SCC "IAddRC" #-}
          unary (+ right) out left >> proceed
        IAddR out in_ -> {-# SCC "IAddR" #-}
          inPlaceBinary (+) out in_ >> proceed
        IAddC out (Constant in_) -> {-# SCC "IAddC" #-}
          inPlaceUnary (+ in_) out >> proceed
        ICall (Labelled _ target) depth _ _ -> {-# SCC "ICall" #-}
          enter depth target
        IEqualsRR out left right -> {-# SCC "IEqualsRR" #-}
          binary (bool .: (==)) out left right >> proceed
        IEqualsRC out left (Constant right) -> {-# SCC "IEqualsRC" #-}
          unary (bool . (== right)) out left >> proceed
        IEqualsR out in_ -> {-# SCC "IEqualsR" #-}
          inPlaceBinary (bool .: (==)) out in_ >> proceed
        IEqualsC out (Constant in_) -> {-# SCC "IEqualsC" #-}
          inPlaceUnary (bool . (== in_)) out >> proceed
        IJump (Labelled _ target) -> {-# SCC "IJump" #-}
          jump target
        IJumpIfZero register (Labelled _ target) (Labelled _ next)
          -> {-# SCC "IJumpIfZero" #-} do
          value <- readRegister register
          jump $ if value == 0 then target else next
        ILessThanRR out left right -> {-# SCC "ILessThanRR" #-}
          binary (bool .: (<)) out left right >> proceed
        ILessThanRC out left (Constant right) -> {-# SCC "ILessThanRC" #-}
          unary (bool . (< right)) out left >> proceed
        ILessThanR out in_ -> {-# SCC "ILessThanR" #-}
          inPlaceBinary (bool .: (<)) out in_ >> proceed
        ILessThanC out (Constant in_) -> {-# SCC "ILessThanC" #-}
          inPlaceUnary (bool . (< in_)) out >> proceed
        IMultiplyRR out left right -> {-# SCC "IMultiplyRR" #-}
          binary (*) out left right >> proceed
        IMultiplyRC out left (Constant right) -> {-# SCC "IMultiplyRC" #-}
          unary (* right) out left >> proceed
        IMultiplyR out in_ -> {-# SCC "IMultiplyR" #-}
          inPlaceBinary (*) out in_ >> proceed
        IMultiplyC out (Constant in_) -> {-# SCC "IMultiplyC" #-}
          inPlaceUnary (* in_) out >> proceed
        INegateR out in_ -> {-# SCC "INegateR" #-}
          unary negate out in_ >> proceed
        INegate out -> {-# SCC "INegate" #-}
          inPlaceUnary negate out >> proceed
        INotR out in_ -> {-# SCC "INotR" #-}
          unary (bool . (== 0)) out in_ >> proceed
        INot out -> {-# SCC "INot" #-}
          inPlaceUnary (bool . (== 0)) out >> proceed
        IReturn result -> {-# SCC "IReturn" #-} do
          csp' <- pred <$> readIORef csp
          result' <- readRegister result
          if csp' < 0 then halt result' else leave result'
        ISetRR out in_ -> {-# SCC "ISetRR" #-}
          unary id out in_ >> proceed
        ISetRC register (Constant constant) -> {-# SCC "ISetRC" #-}
          writeRegister register constant >> proceed

      case action of
        Proceed -> modifyIORef' pc succ >> loop
        Resume -> loop
        Halt value -> return value

    in loop

  where
  callStackSize = (2::Int) ^ (12::Int)
  valueStackSize = (2::Int) ^ (20::Int)
