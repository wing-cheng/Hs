module Ex05 where

import Data.List
import Control.Monad.State (State, get, put, evalState)

-- Task 1. Eight Queens on a Chessboard

-- The queen ♛ is the most powerful piece in the game of chess.
-- Chess is played on an 8x8 checkerboard: each square of the board
-- is labeled by a horizontal and a vertical coordinate ranging from
-- 0 to 7.
--
-- When a queen is placed in one of the squares, it is able to
-- threaten any number of squares vertically, horizontally or
-- diagonally (corner-by-corner) along a straight line.
--
-- For example, the queen Q placed at (1,1) below is able to threaten
-- all the `#` squares, but not the `-` squares.
--
--  0 1 2 3 4 5 6 7
--0 # # # - - - - -
--1 # Q # # # # # #
--2 # # # - - - - -
--3 - # - # - - - -
--4 - # - - # - - -
--5 - # - - - # - -
--6 - # - - - - # -
--7 - # - - - - - #
--
-- The eight queens puzzle is the problem of placing eight chess
-- queens on the checkerboard in such a way that no two of the
-- queens threaten each other's location.
--
-- In a valid solution of the eight queens problem, no two
-- queens can share the same row, column, or diagonal. Since there
-- are eight columns, each column must therefore contain exactly
-- one queen.
--
-- Thus, we will represent our solution as a list `[Int]`
-- of positions: the first entry of the list tells us the location
-- (a row between 0 and 7) of the queen in column 0,
-- the second entry the location of the queen in column 1, and so on.
--
-- A list of length less than 8 denotes a partial solution, where
-- queens were only placed in the first few columns.

type Row = Int
type Queens = [Row] -- position of queen in each column

-- 1.a. Implement a function `extend` that takes a single partial solution
--      containing `n` queens in the first `n` columns, and
--      returns a list of all valid extensions of the partial
--      solution by adding a new queen to the `n+1`st column.
--      If there are no such extensions, the function should return [].
--      HINT 1: write a function that determines safe and threatened
--              row positions in the column.
--      HINT 2: you may want to use the list monad.

threats :: Queens -> [Row]
threats qs
    | len == 8 || len == 0 = []
    | len > 8 = error "Board size must be 8 x 8!"
    where len = length qs
threats xs = nub $ filter (\x -> x >= 0 && x < 8) (threats_helper (length xs) xs)

threats_helper :: Int -> Queens -> [Row]
threats_helper _ [] = []
threats_helper 0 _ = []
-- 'n' denotes how far current col is from 'n+1' col
threats_helper n (x:xs) = [x, x+n, x-n] ++ (threats_helper (n-1) xs)


safes :: Queens -> [Row]
safes qs
    | len == 0 || len == 8 = []
    | len > 8 = error "Board size must be 8 x 8!"
    where len = length qs
safes qs = filter (\x -> x `notElem` ts) [0..7] 
    where ts = threats qs

extend :: Queens -> [Queens]
extend qs
    | len == 0 = [[x] | x <- [0..7]]
    | len == 8 = [qs]
    | len > 8 = error "Board size must be 8 x 8!"
    where len = length qs
extend qs = map (toTail qs) (safes qs)
    where
        toTail :: [a] -> a -> [a]
        toTail [] e = [e]
        toTail (x:xs) e = x:(toTail xs e)

-- 1.b. Implement a function that, given a row position `p`,
--      returns the list of all possible solutions to the eight
--      queens problem in which the queen in the first column
--      is placed in the row position `p`.
solutionStartWith :: Int -> [Queens]
-- solutionStartWith = error "'solutionStartWith' not implemented"
solutionStartWith loc
    | loc > 7 || loc < 0 = []
    | otherwise =
        extend [loc] >>= 
        extend >>= 
        extend >>= 
        extend >>= 
        extend >>= 
        extend >>= 
        extend >>= 
        extend



-- Task 2. RPN calculator
-- Reverse Polish notation (RPN) is a way of writing arithmetic
-- expressions without parentheses. Apart from the lack
-- of parentheses, its main advantage is that it's easy
-- to type into a calculator.
--
-- Handheld RPN calculators were very popular throughout the 80s,
-- and some people still swear by them.
--
-- Generally, evaluation on an RPN calculator proceeds by maintaining
-- a stack of numbers, and handling each user action one at a time.
-- 1. If the user entered a number (e.g. action `Enter 5`),
--    we push the entered number onto a stack.
-- 2. If the user pressed the button for an arithmetic operation,
--    say `+`, we remove the two topmost number `x` and `y` from
--    the stack, and put the result, (in this case `y + x`) on
--    the stack.
-- 3. There are special buttons: `Clear`, which, when pressed, removes
--    the topmost number from the stack; `AllClear`, which removes
--    everything from the stack, and `Swap`, which swaps the two
--    topmost elements on the stack.

-- Old calculators could store only 4-5 elements on their stack.
-- Here, we allow our stack to be an unbounded list of numbers.
-- The bottom of the stack is always padded with zeroes:
-- so the stack `[]` and the stack `[0,0]` behave identically,
-- as the stacks `[5,4]` and `[5,4,0]` behave identically as well.

-- As an example, the following sequence of actions:
-- `[Enter 3, Enter 7, Enter 5, Arith (-), Arith (*)]`
-- will result in the following final stack state: [6].
-- First, 3, 7 and 5 are put on the stack. Then we subtract
-- 5 from 7, leaving 3 and 2 on the stack. Finally, we multiply
-- these two, which yields 6.

type Stack = [Double]

data UserAction
  = Arith (Double -> Double -> Double)
  | Clear
  | AllClear
  | Swap
  | Enter Double

push :: Double -> State Stack ()
push x =
  get        >>= \xs ->
  put (x:xs)

-- 2.a. Implement the pop operation which removes and returns
--      the top element of the stack. Keep in mind that empty
--      stacks are treated as if they were padded with zeroes.
pop :: State Stack Double
pop = 
    get >>= \xs ->
    case xs of
        [] -> return 0
        otherwse -> 
            put (tail xs) >>= \_ -> -- same as: put (tail xs) >>
            return (head xs)
pop_do :: State Stack Double
pop_do = do
    xs <- get
    put (tail xs)
    return (head xs)

-- The Clear user action lets the user remove the top element
-- of the current stack.
clear :: State Stack ()
clear =
  pop        >>= \_ ->
  return ()

-- 2.b. Implement the AllClear user action, which removes all
--      elements from the stack.
allClear :: State Stack ()
allClear = put []

-- 2.c. Implement the Swap user action, which switches the order
--      of the two topmost elements in the stack. Keep in mind
--      that empty stacks are zero-padded.
swap :: State Stack ()
swap =
    get >>= \xs ->
    case xs of
        [] -> return ()
        [x] -> push 0
        otherwise ->
            pop >>= \e1 ->
            pop >>= \e2 ->
            push e2 >>
            push e1
swap_do :: State Stack ()
swap_do = do
    xs <- get
    case xs of
        [] -> do return ()
        [x] -> do push 0
        otherwise -> do
            e1 <- pop
            e2 <- pop
            push e2
            push e1


-- 2.d. Implement the `Arith` user action, which performs the
--      given arithmetic operation on the top two elements of
--      the stack. E.g. if the stack contains `[2,3]`, then
--      `Arith (-)` should result in `[1]`.
performArith :: (Double -> Double -> Double) -> State Stack ()
performArith op =
    pop >>= \e1 ->
    pop >>= \e2 ->
    push (op e2 e1)

performArith_do :: (Double -> Double -> Double) -> State Stack ()
performArith_do op = do
    e1 <- pop        
    e2 <- pop
    push (op e2 e1)

-- 2.e. Implement the `app1` function, which applies the given
--      user action to the current stack.
app1 :: UserAction -> State Stack ()
app1 (Arith op) = (performArith op)
app1 Clear = clear
app1 AllClear = allClear
app1 Swap = swap
app1 (Enter n) = push n

-- 2.f. Implement the `app` function, which applies the given
--      list of user actions, in order, starting with the head
--      of the list. Once all actions are perforemd, it returns
--      the final state of the stack.
app :: [UserAction] -> State Stack Stack
app [] = get
app (x:xs) = app1 x >> app xs


-- you can use `runCalc` to test your implementation. E.g.
-- *> runCalc [Enter 3, Enter 7, Enter 5, Arith (-), Arith (*)]
-- [6.0]
runCalc :: [UserAction] -> Stack
runCalc xs = evalState (app xs) []

