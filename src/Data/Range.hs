{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Data.Range
  ( Range(rangeStart, rangeEnd, rangeFile)
  , SourcePos(..), mkPos, unPos
  , newRange
  , newRangeUnchecked
  , includes

  , intervalToRange, rangeToInterval
  ) where

import Text.Megaparsec.Pos
import Data.Hashable
import GHC.Generics 
import Data.IntervalMap.FingerTree (Interval(..))

data Range =
  Range { rangeStart :: SourcePos
        , rangeEnd   :: SourcePos
        , rangeFile  :: String
        }
  deriving (Eq, Show, Ord, Generic)

instance Hashable Range where
  -- SourcePos/Pos aren't Hashable
  hashWithSalt salt (Range (SourcePos _ aa ab) (SourcePos _ ba bb) file) =
    salt `hashWithSalt` unPos aa
         `hashWithSalt` unPos ab
         `hashWithSalt` unPos ba
         `hashWithSalt` unPos bb
         `hashWithSalt` file

newRange :: SourcePos -> SourcePos -> Maybe Range
newRange a b
  | sourceName a == sourceName b = Just (newRangeUnchecked a b)
  | otherwise = Nothing

newRangeUnchecked :: SourcePos -> SourcePos -> Range
newRangeUnchecked a b =
  let start = min a b
      end = max a b
   in Range start end (sourceName a)

instance Semigroup Range where
  Range a _ l <> Range _ b _ = Range a b l

includes :: Range -> Range -> Bool
includes (Range bigStart bigEnd l) (Range smallStart smallEnd l') =
     l == l'
  && smallStart >= bigStart
  && smallEnd <= bigEnd

rangeToInterval :: Range -> Interval SourcePos
rangeToInterval (Range a b _) = Interval a b

intervalToRange :: Interval SourcePos -> Range
intervalToRange (Interval a b) = newRangeUnchecked a b