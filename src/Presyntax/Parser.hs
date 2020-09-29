{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
module Presyntax.Parser where

import Data.Range

import Presyntax.Lexer
import Presyntax
import Data.Text (Text)
import Data.Foldable
import Control.Exception (throwIO)
import qualified Text.Megaparsec.Char.Lexer as L

loc :: Parser a -> Parser (L a)
loc k = do
  start <- getSourcePos
  x <- k
  end <- getSourcePos
  pure (L x (newRangeUnchecked start end))

var :: Parser Var
var = Intro <$> identifier

set :: Parser Int
set =
  lexeme $ do
    _ <- string "Type"
    (char '{' *> normalscript <* char '}') <|> subscript
  where
    normalscript = fromInteger <$> lexeme decimal
    subscriptDigit =
      foldl (<|>) empty
        (zipWith (\l c -> l <$ char c) [0..9] ['₀'..'₉'])
      <?> "unicode subscript digit"
    subscript = foldl' (\c x -> c * 10 + x) 0 <$> some subscriptDigit

atom, expr, expr0 :: Parser (ExprL Var)
atom = loc (Set <$> set)
   <|> loc (Var <$> var)
   <|> loc (Hole <$ symbol "_")
   <|> parens expr

expr0 = loc lambda <|> loc (try quantifier) <|> atom

quantifier :: Parser (Expr L Var)
quantifier = pi where
  binder = parens $ (,) <$> identifier <*> (colon *> expr)
  pi = do
    (name, ty) <- binder
    x <- optional arrow
    Pi (Intro name) ty <$> case x of
      Nothing -> loc pi
      Just _ -> expr

lambda :: Parser (Expr L Var)
lambda = 
  do
    _ <- lexeme (char 'λ' <|> char '\\')
    lambdaForm
  where
    lambdaForm :: Parser (Expr L Var)
    lambdaForm = do
      x <- identifier
      t <- optional arrow
      Lam (Intro x) <$> case t of
        Nothing -> loc lambdaForm
        Just _ -> expr

expr =
  do
    head <- expr0
    atoms <- many applied
    pure (app head atoms)
  where
    app head [] = head
    app head ((vis, a):rest) = app (L (App vis head a) (lRange head <> lRange a)) rest

    applied = ((,) True <$> braces expr0) <|> ((,) False <$> expr0)

decl :: Parser (L (Decl L Var))
decl =
  dataDecl <|> do
    id <- var
    col <- optional colon
    loc $
      case col of
        Nothing -> Value id <$> definition
        Just _ -> fmap (TypeSig id) expr
  where
    definition = do
      c <- optional equals
      case c of
        Nothing -> loc $ Lam <$> var <*> definition
        Just _ -> expr

dataDecl :: Parser (L (Decl L Var))
dataDecl = loc $ L.indentBlock cuboSpaceN parseHeader where
  parseHeader = do
    _ <- symbol "data"
    eliminator <- parens var
    name <- var
    params <- many (loc (parens ((,) <$> (var <* colon) <*> expr)))
    _ <- colon
    kind <- expr
    _ <- symbol "where"
    pure (L.IndentMany Nothing (pure . DataDecl name eliminator params kind) parseConstructor)
  
  parseConstructor :: Parser (L (Var, L (Expr L Var)))
  parseConstructor = loc ((,) <$> var <*> (colon *> expr))

parseFileIO :: String -> Text -> IO [L (Decl L Var)]
parseFileIO source contents =
  case parse (prog <* eof) source contents of
    Left bundle -> throwIO (ParseError bundle)
    Right x -> pure x
  where
    prog = many (L.nonIndented cuboSpaceN decl <* many newline)