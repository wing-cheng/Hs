module Size (Size, size, unSize) where

data Size
  = Size Integer
  deriving (Show, Eq, Ord)

wf :: Size -> Bool
wf (Size x) = x >= 0

size :: Integer -> Size
size x
  | x < 0     = error "size: cannot be negative"
  | otherwise = Size x

unSize :: Size -> Integer
unSize (Size x) = x

instance Semigroup Size where
  Size x <> Size y = Size (x + y)

instance Monoid Size where
  mempty = Size 0
  mappend = (<>)
