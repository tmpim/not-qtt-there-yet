{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Presyntax.Context where

import GHC.Generics (Generic)
import Data.Hashable

data SyntaxContext
  = ArgumentContext
  | FunctionContext
  | BodyContext
  | RangeContext
  deriving (Eq, Show, Ord, Generic, Hashable)

contextPrecedence :: SyntaxContext -> Int
contextPrecedence BodyContext = 0
contextPrecedence RangeContext = 0
contextPrecedence ArgumentContext = 2
contextPrecedence FunctionContext = 2