module Tortoise where

-- COMP3141 22T2 ASSIGNMENT 1

import Data.Semigroup
import Data.List
import Test.QuickCheck

-- data type definitions

data Freq = Freq Int deriving (Show, Eq, Ord)
data Interval = Interval Int deriving (Eq, Ord)

type Count = Integer
data Histogram = Histogram [(Interval, Count)] deriving (Show, Eq)

data SigCard = SigCard {
    refHistogram :: Histogram,
    excluded :: [Interval]
} deriving (Show, Eq)

data Verdict = RealWeapon | Dud deriving (Show, Eq)

-- helper functions

notImpl :: String -> a
notImpl x = error $ "'" ++ x ++ "'" ++ " not defined"

startPoint :: Interval -> Freq
startPoint (Interval x) = Freq (100*x)

endPoint :: Interval -> Freq
endPoint (Interval x) = Freq (100*x + 100)

-- ASSIGNMENT STARTS HERE --

-- Problem 1.a
inside :: Freq -> Interval -> Bool
(Freq x) `inside` (Interval r) = x >= (r * 100) && x < (r + 1) * 100 

-- Problem 1.b
-- redefine show for Interval
instance Show Interval where
    show (Interval r) = show (r * 100) ++ " to " ++ show (r * 100 + 100)

intervalOf :: Freq -> Interval
intervalOf (Freq f) = Interval (f `div` 100) 

-- Problem 1.c

-- define (Arbitraty Freq) instance
largeToFreq :: Large Int -> Freq
largeToFreq (Large n) = Freq (n)
instance Arbitrary Freq where
    arbitrary = largeToFreq <$> abs <$> arbitrary

-- define (Arbitrary Interval) instance
instance Arbitrary Interval where
    arbitrary = Interval <$> abs <$> arbitrary


prop_inIntervalOf :: Freq -> Bool
prop_inIntervalOf f = f `inside` intervalOf f

prop_inOneInterval :: Freq -> Interval -> Property
-- if f `inside` r then r == intervalOf f
-- if f not `inside` r then 
prop_inOneInterval f r = not (f `inside` r) ==> r /= intervalOf f
    

-- Problem 2

histogram :: [(Interval, Count)] -> Histogram
-- 1. remove zero or negative Count
-- 2. include any one of the Intervals that occur more than once
-- 3. Intervals in ascending order
histogram xs = Histogram $
    nubBy (\(Interval a, _) (Interval b, _) -> a == b) $
    sortBy (\(Interval a, _) (Interval b, _) -> a `compare` b) $
    filter (\(_, c) -> c > 0) xs


{-
    since haskell already know how to generate Interval and Count (just Interger)
    it can automatically generate Histogram, all we need to do is just parsing the list
-}

instance Arbitrary Histogram where
    arbitrary = histogram <$> arbitrary
-- instance Arbitrary SigCard where
    -- arbitrary = arbitrary

-- test if zero or negative Count not present
prop_histogram1 :: Histogram -> Bool
prop_histogram1 (Histogram xs) = prop_histogram1_helper xs
prop_histogram1_helper :: [(Interval, Count)] -> Bool
prop_histogram1_helper [] = True
prop_histogram1_helper (x:xs) = snd x > 0 && prop_histogram1_helper xs

-- test exacly one occurence of each Interval 
prop_histogram2 :: Histogram -> Bool
-- extract the Intervals and compare the original and the nub result
prop_histogram2 (Histogram xs) = nub itvs == itvs where
  itvs = map (\x -> fst x) xs

-- test if Intervals are in ascending order
prop_histogram3 :: Histogram -> Bool
prop_histogram3 (Histogram []) = True
prop_histogram3 (Histogram [x]) = True
prop_histogram3 (Histogram hs) = hs == sortBy (\(Interval r1, _) (Interval r2, _) -> compare r1 r2) hs


-- Problem 3

process :: [Freq] -> Histogram
-- process [] = histogram []
process fs = histogram $ process_helper2 fs $ process_helper1 fs

process_helper1 :: [Freq] -> [Interval]
process_helper1 = map (\(Freq x) -> Interval (x `div` 100))

process_helper2 :: [Freq] -> [Interval] -> [(Interval, Count)]
process_helper2 fs itvs = map (\(i, c) -> (i, toInteger c)) tmp where
    tmp = map (\x -> (x, length $ filter (`inside` x) fs)) itvs 

merge :: Histogram -> Histogram -> Histogram
merge (Histogram a) (Histogram b) = process $ all_freqs (a ++ b)

all_freqs :: [(Interval, Count)] -> [Freq]
all_freqs [] = []
all_freqs ((Interval i, c):xs) = replicate (fromIntegral c) (Freq (i * 100)) ++ all_freqs xs
        

prop_mergeAssoc :: Histogram -> Histogram -> Histogram -> Bool
prop_mergeAssoc a b c = merge (merge a b) c == merge a (merge b c)

prop_mergeId :: Histogram -> Bool
prop_mergeId a = merge (Histogram []) a == a && merge a (Histogram []) == a


b = Histogram [(Interval 0,3),(Interval 2,3)]
a = Histogram [(Interval 0,2),(Interval 2,2)]
prop_mergeComm :: Histogram -> Histogram -> Bool
prop_mergeComm a b = merge a b == merge b a

instance Semigroup Histogram where
    (<>) = merge
instance Monoid Histogram where
    mappend = (<>)
    mempty = Histogram []


-- Problem 4

report_refl :: Maybe Histogram
report_refl = Nothing

report_symm :: Maybe (Histogram, Histogram)
report_symm = Nothing

x1 = Histogram [(Interval 1, 0)]
x2 = Histogram [(Interval 1, 31)]
x3 = Histogram [(Interval 1, 62)]
report_tran :: Maybe (Histogram, Histogram, Histogram)
report_tran = Just (x1, x2, x3)

-- Inspector O'Hare implemented match as follows:
match :: Histogram -> SigCard -> Verdict
match (Histogram h) (SigCard (Histogram r) v) =
    if d < 32 then RealWeapon else Dud where
        grab r (Histogram hs) = case filter (\x -> fst x == r) hs of
            [(_,x)] -> x
            _       -> 0
        squareDist (Histogram h1) (Histogram h2) = sum squares where
            common = sort . nub $ map fst h1 ++ map fst h2
            squares =
                map (\x -> (fromIntegral $ grab x (Histogram h1) - grab x (Histogram h2))**2)
                    common
        d1 = squareDist (Histogram h) (Histogram r)
        h' = Histogram $ filter (\x -> fst x `elem` v) h
        r' = Histogram $ filter (\x -> fst x `elem` v) r
        d2 = squareDist h' r'
        d = sqrt (d1 - d2)



-- Use this reference card to find a false positive for `match`
refCard :: SigCard
refCard = SigCard (histogram r) v where
  r = [(Interval 4, 4000), (Interval 5, 6000), (Interval 6, 300)]
  v = [Interval 5]


-- dud weapons that nevertheless pass the match process as if they were real weapons.
falsePos :: Histogram
falsePos = Histogram [
    (Interval 4, 700),
    (Interval 5, 600000000000000),
    (Interval 6, 200)]
