{-#
  LANGUAGE DataKinds
  , NoMonomorphismRestriction
  #-}

module Parse
  ( parse
  ) where

import Compiler.Hoopl hiding ((<*>))
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Text.Parsec hiding (State, (<|>), label, labels, many, parse)
import Text.Parsec.Text.Lazy ()

import qualified Data.Text.Lazy as Lazy
import qualified Data.Vector as Vector

import IdMap
import Instruction
import Types

-- | Parses a source file containing "simple register machine" assembly into a
-- 'FlatProgram' containing only basic (non-'Optimized') instructions.
parse
  :: SourceName  -- ^ Source file name, for Parsec's error reporting.
  -> Lazy.Text  -- ^ Input stream.
  -> SimpleUniqueMonad (Either ParseError (FlatProgram Parsed))
parse filename file = liftM snd . runIdMap
  $ runParserT program () filename file
  where
  program = FlatProgram . Vector.fromList
    <$> ((statement `sepEndBy` many1 newline) <* eof)
  statement = horizontals *> target >>= instruction
  instruction pc = do
    current <- lift $ labelForTarget pc
    next <- let pc' = succ pc
      in Labelled <$> lift (labelForTarget pc') <*> pure pc'
    Labelled current <$> (medial <|> final next)
    where
    medial = choice
      [ IAddRR <$ word "Add" <*> registerComma <*> registerComma <*> register
      , register3 (word "Equals") IEqualsRR
      , register3 (word "LessThan") ILessThanRR
      , try $ register2 (word "Move") ISetRR
      , register3 (word "Multiply") IMultiplyRR
      , try $ register2 (word "Negate") INegateR
      , register2 (word "Not") INotR
      , ISetRC <$ word "Set" <*> registerComma <*> constant
      ]
    final next = choice
      [ ICall <$ word "Call"
        <*> (label <* comma) <*> (depth <* comma) <*> register <*> pure next
      , try $ IJump <$ word "Jump" <*> label
      , IJumpIfZero <$ word "JumpIfZero"
        <*> registerComma <*> label <*> pure next
      , IReturn <$ word "Return" <*> register
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
    = register2 mnemonic constructor <*> (comma *> register)
  registerComma = register <* comma
  lexeme = (<* horizontals)
  word = lexeme . string
  comma = word ","
  horizontal = oneOf " \t"
  horizontals = many horizontal
