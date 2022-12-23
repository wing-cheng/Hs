module Priority (Priority, priority, unPriority) where

import Data.Semigroup
import Data.Monoid

import Test.QuickCheck

data Priority
  = Priority Integer
  deriving (Show, Eq)

wf :: Priority -> Bool
wf (Priority x) = x >= 0

priority :: Integer -> Priority
priority x
  | x < 0     = error "priority: cannot be negative"
  | otherwise = Priority x

unPriority :: Priority -> Integer
unPriority (Priority x) = x

instance Semigroup Priority where
  Priority x <> Priority y = Priority (max x y)

instance Monoid Priority where
  mempty = Priority 0
  mappend = (<>)

instance Arbitrary Priority where
  arbitrary = (\(NonNegative x) -> priority x) <$> arbitrary
