module Data.HashMap.Compat
  ( module HM
  , withoutKeys
  )
  where

import qualified Data.HashSet as HS
import Data.HashMap.Strict as HM
import Data.Hashable


withoutKeys :: (Eq a, Hashable a) => HM.HashMap a v -> HS.HashSet a -> HM.HashMap a v
withoutKeys map set = HM.filterWithKey (\k _ -> not (HS.member k set)) map