{-# LANGUAGE OverloadedStrings #-}
module Presyntax.Lexer
  ( module P

  , Parser
  , lexeme
  , symbol
  , parens
  , braces
  , comma, colon, cutcolon, arrow, semicolon, semisemi, equals
  , identifier
  , decimal
  , cuboSpace, cuboSpaceN

  , ParseException(..)
  ) where

import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char as P
import Text.Megaparsec as P

import qualified Data.HashSet as HashSet
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.HashSet (HashSet)
import Data.Text (Text)
import Data.Void (Void)

import Control.Monad (when)
import Control.Exception (Exception(..))
import Data.Coerce (coerce)
import Data.Char (isSpace)

type Parser = Parsec Void Text

cuboSpaceN :: Parser ()
cuboSpaceN = L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

cuboSpace :: Parser ()
cuboSpace = L.space (() <$ takeWhile1P Nothing f) (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}") where
  f x = x /= '\n' && isSpace x

lexeme :: Parser a -> Parser a
lexeme = L.lexeme cuboSpace

symbol :: Text -> Parser Text
symbol = L.symbol cuboSpace

parens, braces :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

comma, colon, cutcolon, arrow, semicolon, semisemi, equals :: Parser Text
comma     = symbol ","
colon     = symbol ":"
cutcolon  = symbol "::"
semicolon = symbol ";"
arrow     = symbol "->" <|> lexeme (T.singleton <$> char '→')
semisemi  = symbol ";;"
equals    = symbol "="

decimal :: Parser Integer
decimal = lexeme L.decimal

programWord :: Parser Text
programWord = lexeme (takeWhile1P (Just "an identifier") pred) where
  pred :: Char -> Bool
  pred ch = ('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z')

keywords :: HashSet Text
keywords = HashSet.fromList ["where", "data"]

identifier :: Parser Text
identifier = do
  x <- lookAhead programWord
  when (x `HashSet.member` keywords) $ do
    failure (Just (Tokens (T.head x :| T.unpack (T.tail x))))
            (Set.singleton (Label ('a' :| "n identifier")))
  _ <- programWord
  pure x

newtype ParseException = ParseError (ParseErrorBundle Text Void)
  deriving (Eq)

instance Show ParseException where
  show = coerce errorBundlePretty

instance Exception ParseException where
  displayException = coerce errorBundlePretty