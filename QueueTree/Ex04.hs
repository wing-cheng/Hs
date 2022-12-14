module Ex04 where

import Data.Semigroup
import Data.Monoid
import Control.Monad.State (State, get, put, evalState, runState, execState)
import Data.Tuple (swap)
import Test.QuickCheck
import Priority
import Size

-- DEFINITIONS AND HELPER FUNCTIONS --

type NodeInfo = (Size, Priority)
data QueueTree a
    = Null
    | Leaf NodeInfo a
    | Node NodeInfo (QueueTree a) (QueueTree a)
    deriving (Show, Eq)

nodeInfo :: QueueTree a -> NodeInfo
nodeInfo Null = mempty
nodeInfo (Leaf i _) = i
nodeInfo (Node i _ _) = i

sizeOf :: QueueTree a -> Size
sizeOf = fst . nodeInfo

minusSize :: Size -> Size
minusSize s1 = s1 <> size (-1)

plusSize :: Size -> Size
plusSize s1 = s1 <> size 1

maxPrio :: QueueTree a -> Priority
maxPrio = snd . nodeInfo

-- checks whether the tree structure
-- is balanced (i.e. that the left subtree and the right
-- subtree don't ever differ too much in size)
balanced :: QueueTree a -> Bool
balanced (Node i l r) =
    let sl = unSize (sizeOf l) in
    let sr = unSize (sizeOf r) in
    abs (sl - sr) <= 1 && balanced l && balanced r
balanced _ = True



-- EXERCISE STARTS HERE --

-- Task 1a. Write a well-formedness predicate
--          wf for the `QueueTree` data type.

-- Hint: Both `Priority` and `Size` are semigroups/monoids.
-- This means that the type `NodeInfo` is also automatically
-- a monoid.

max_priority :: QueueTree a -> Integer
max_priority (Leaf (_, p) _) = unPriority p
max_priority (Node (_, _) l r) =
    max (max_priority l) (max_priority r)

num_leaves :: QueueTree a -> Integer
num_leaves Null = 0
num_leaves (Node _ l r) = (num_leaves l) + (num_leaves r)
num_leaves (Leaf _ _) = 1

wf :: QueueTree a -> Bool
-- leaf can only be of size 1
wf Null = True
wf (Leaf (s, p) a) = unPriority p >= 0 && unSize s == 1
wf (Node (s, p) l r) =
    unPriority p >= 0 &&
    unSize s > 0 &&
    unSize s == (num_leaves l) + (num_leaves r) &&
    p == maxPrio l <> maxPrio r &&
    wf l &&
    wf r



-- Task 1b. Write smart constructors `leaf` and `node`
--          for the `QueueTree` data type which maintain
--          the well-formedness invariant. I.e. given
--          well-formed inputs, the smart constructors
--          should give well-formed outputs.
leaf :: Priority -> a -> QueueTree a
leaf p v = Leaf (size 1, p) v
node :: QueueTree a -> QueueTree a -> QueueTree a
node l r = Node (sizeOf l <> sizeOf r, ((maxPrio l) <> (maxPrio r))) l r



-- Task 2a. Implement the usual priority queue functions
--          for the type `QueueTree`. These are
--          pop - Remove the element from the queue that has the
--               highest priority. Return the modified queue,
--               along with the removed element (if any).
--          insert - add an element to the queue with the given priority.

pop :: QueueTree a -> (QueueTree a, Maybe a)
-- go to the side with equal priority to the current node
-- assume that the input tree is well-formed
pop (Leaf _ v) = (Null, Just v)
pop Null = (Null, Nothing)
pop (Node (s, p) Null Null) = error "QueueTree is not well-formed!"
-- right is NOT Null
pop (Node (s, p) Null r) = let cur_prio = unPriority p in
    case maxPrio r of
        cur_prio -> let
                pop_res = pop r
                fst_pop_res = fst pop_res
            in case fst_pop_res of
                Null -> (Null, snd pop_res)
                otherwise -> (Node (minusSize s, maxPrio fst_pop_res) Null fst_pop_res, snd pop_res)
        otherwise -> error "QueueTree is not well-formed!"
-- assume left is NOT Null
pop (Node (s, p) l Null) = let cur_prio = unPriority p in
    case maxPrio l of
        cur_prio -> let
                pop_res = pop l
                fst_pop_res = fst pop_res
            in case fst_pop_res of
                Null -> (Null, snd pop_res)
                otherwise -> (Node (minusSize s, maxPrio fst_pop_res) fst_pop_res Null, snd pop_res)
        otherwise -> error "QueueTree is not well-formed!"
-- assume both left and right are NOT Null
pop (Node (s, p) l r) = let cur_prio = unPriority p in
    case maxPrio l of
        cur_prio -> let
                pop_res = pop l
                fst_pop_res = fst pop_res
            in case fst_pop_res of
                Null -> (Node (minusSize s, maxPrio fst_pop_res <> maxPrio r) Null r, snd pop_res)
                otherwise -> (Node (minusSize s, maxPrio fst_pop_res) fst_pop_res r, snd pop_res)
        otherwise -> case maxPrio r of
            cur_prio -> let
                    pop_res = pop r
                    fst_pop_res = fst pop_res
                in case fst_pop_res of
                    Null -> (Node (minusSize s, maxPrio fst_pop_res <> maxPrio l) l Null, snd pop_res)
                    otherwise -> (Node (minusSize s, maxPrio fst_pop_res) l fst_pop_res, snd pop_res)
            otherwise -> error "QueueTree is not well-formed!"
            


insert :: Priority -> a -> QueueTree a -> QueueTree a
insert p v Null = leaf p v
insert p v (Node (s', p') Null Null) = error "QueueTree is not well-formed!"
insert p v (Node (s', p') l Null) = Node (plusSize s', p <> p') l (Leaf (size 1, p) v)
insert p v (Node (s', p') Null r) = Node (plusSize s', p <> p') (Leaf (size 1, p) v) r
-- assume that both left and right sub-tree are NOT Null
-- insert to the side with smaller size
insert p v (Node (s, p') l r) =
    case lh <= rh of
        True -> Node (s <> size 1, (p <> p')) (insert p v l) r
        False -> Node (s <> size 1, (p <> p')) l (insert p v r)
        where
            lh = sizeOf l
            rh = sizeOf r
-- insert to leaf
-- put the input leaf to LHS and insert a new leaf to RHS
insert p v leaf' = Node (size 2, maxPrio leaf' <> p) leaf' (leaf p v)



-- Task 2b. Implement a function `fromList` that converts a
--          list of `(Priority, x)` pairs into a well-formed
--          and balanced `QueueTree x` structure.
fromList :: [(Priority, a)] -> QueueTree a
fromList [] = Null
fromList ((p, q):xs) = insert p q (fromList xs)

-- Hint: you can use `fromList` to implement an `Arbitrary`
-- instance for `QueueTree`, allowing you to test your work.
-- instance Arbitrary a where
    -- arbitrary = Char
-- instance Arbitrary (QueueTree a) where
    -- arbitrary = fromList <*> [arbitrary]
-- instance Arbitrary (QueueTree a) where
    -- arbitrary = fromList <$> [(arbitrary, arbitrary :: Char)]

-- Task 3. Implement stateful versions of the pop and insert
--         operations above using the `State` type in Haskell's
--         standard mtl library.
--         Implement a `peek` operation which just returns the
--         highest-priority element without changing the
--         state of the queue.
--         Do not use the `state` function in your final
--         implementations!

pop' :: State (QueueTree a) (Maybe a)
-- pop' = error "'pop'' not implemented"
pop' =
    get >>= \qt ->
    let
        pop_res = pop qt
    in 
    put (fst pop_res) >>    -- same as: put t >>= \() ->
    return (snd pop_res)
-- pop' quickCheck
qcheck_pop' :: Eq a => QueueTree a -> Bool
qcheck_pop' t = swap (runState pop' t) == pop t


pop_do :: State (QueueTree a) (Maybe a)
pop_do = do
    t <- get
    let pop_res = pop t
    put (fst pop_res)
    return (snd pop_res)
-- pop_do quickCheck
qcheck_pop_do :: Eq a => QueueTree a -> Bool
qcheck_pop_do t = runState pop' t == runState pop_do t


insert' :: Priority -> a -> State (QueueTree a) ()
insert' p v =
    get >>= \qt ->
    put (insert p v qt)
-- insert' quickCheck
qcheck_insert' :: Eq a => Priority -> a -> QueueTree a -> Bool
qcheck_insert' p v t = execState (insert' p v) t == insert p v t


insert_do :: Priority -> a -> State (QueueTree a) ()
insert_do p v = do
    qt <- get
    put (insert p v qt)
-- insert_do quickCheck
qcheck_insert_do :: Eq a => Priority -> a -> QueueTree a -> Bool
qcheck_insert_do p v t = execState (insert' p v) t == execState (insert_do p v) t


peek' :: State (QueueTree a) (Maybe a)
peek' =
    get >>= \qt ->
    let
        pop_res = pop qt
    in
    put qt >>
    return (snd pop_res)

peak_do :: State (QueueTree a) (Maybe a)
peak_do = do
    qt <- get
    rv <- pop'
    put qt      -- update the state
    return rv   -- update the value


-- END OF EXERCISE --

-- You can use the following three examples to test your
-- implementations of pop' and insert', and to practice
-- reading `State`-ful functions.

-- Returns the highest priority currently in the `QueueTree`
-- without changing the state.
getMaxPrio' :: State (QueueTree a) Priority
getMaxPrio' =
    get >>= \q ->
    return (maxPrio q)

-- Removes the element with the second-highest priority
-- in the queue.
dip' :: State (QueueTree a) ()
dip' =
    getMaxPrio' >>= \p ->
    pop'        >>= \h1 ->
    pop'        >>= \h2 ->
    case h1 of
        Nothing -> return ()
        Just h1 -> insert' p h1

-- a `State`-free version of dip
dip :: QueueTree Char -> QueueTree Char
dip = evalState $
    dip' >>= \() ->
    get
