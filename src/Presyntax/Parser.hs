{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
module Presyntax.Parser where

import Control.Exception (throwIO)

import Data.Text (Text)
import Data.Range
import Data.L

import Presyntax.Lexer
import Presyntax

import Qtt (Visibility(..))

import qualified Text.Megaparsec.Char.Lexer as L


loc :: Parser a -> Parser (L a)
loc k = do
  start <- getSourcePos
  x <- k
  end <- getSourcePos
  pure (L x (newRangeUnchecked start end))

var :: Parser Var
var = Intro <$> identifier

atom, expr, expr0 :: Parser (ExprL Var)
atom = loc (Set <$ symbol "Type")
   <|> loc (Prop <$ symbol "Prop")
   <|> loc (Var <$> var)
   <|> loc (Hole <$ symbol "_")
   <|> parens expr

expr0 = loc lambda <|> loc (try quantifier) <|> atom

quantifier :: Parser (Expr L Var)
quantifier = pi where
  binder = parens ((,,) Visible   <$> loc identifier <*> (colon *> expr))
       <|> braces ((,,) Invisible <$> loc identifier <*> (colon *> expr))
  pi = do
    (vis, name, ty) <- binder
    x <- optional arrow
    Pi vis (Intro <$> name) ty <$> case x of
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
      (v, x) <- ((,) Visible <$> loc identifier) <|> ((,) Invisible <$> braces (loc identifier))
      t <- optional arrow
      Lam v (Intro <$> x) <$> case t of
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

    applied = ((,) Invisible <$> braces expr) <|> ((,) Visible <$> expr0)

decl :: Parser (L (Decl L Var))
decl =
      loc (fmap DataStmt dataDecl)
  <|> loc (Include <$> loc (symbol "#include" *> takeWhile1P (Just "Path name") (/= '\n')))
  <|> do
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
        Nothing -> loc do
          (vis, nam) <- arg
          Lam vis (Intro <$> nam) <$> definition
        Just _ -> expr
    arg = ((,) Visible <$> loc identifier) <|> ((,) Invisible <$> braces (loc identifier))

dataDecl :: Parser (DataDecl L Var)
dataDecl = L.indentBlock cuboSpaceN parseHeader where
  parseHeader = do
    _ <- symbol "data"
    name <- var
    params <- many (loc (parens ((,) <$> (var <* colon) <*> expr)))
    _ <- colon
    kind <- expr
    _ <- symbol "where"
    pure (L.IndentMany Nothing (pure . DataDecl name params kind) parseConstructor)
  
  parseConstructor :: Parser (L (Var, L (Expr L Var)))
  parseConstructor = loc ((,) <$> var <*> (colon *> expr))

parseFileIO :: String -> Text -> IO [L (Decl L Var)]
parseFileIO source contents =
  case parse (prog <* eof) source contents of
    Left bundle -> throwIO (ParseError bundle)
    Right x -> pure x
  where
    prog = many (L.nonIndented cuboSpaceN decl <* many newline)