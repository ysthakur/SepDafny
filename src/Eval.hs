-- | An Interpreter for MiniDafny |
--   ================================
--
-- In this problem, you will use the state monad to build an *interpreter* and a stepper for
-- our simple imperative language.
module Eval where

-- \|
-- This assignment uses the State Monad module from the standard library.
--
-- Because the MiniDafny language includes variables, we'll also use the finite
--  maps from Haskell's containers library (Data.Map) to represent the store.
--

import Control.Monad (forM_, guard, when)
import Control.Monad.State
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Syntax
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Text.Read (readMaybe)

-- | The MiniDafny Store |
--   -----------------------
--
-- One component of the interpreter is a *store* that represents our computer's
-- memory or heap during the evaluation of MiniDafny prorams. We represent this store
-- as an associative map from variable `Name`s to `Values`:
type Store = Map Name Value

-- | When the evaluator starts, the initial store will be empty,
-- and will be updated with any variables passed in as arguments
-- before evaluating a method.
initialStore :: Store
initialStore = Map.empty

-- |
-- During computation, the store could be extended to include new mappings for
-- global variables. For example, if we called a method with a
-- parameter "x" with the integer 3, a parameter "a" corresponding to the array
-- with elements from one to four, and then allocated a new local variable
-- "y" with the value `True`, then the store will look like this:
extendedStore :: Store
extendedStore =
  Map.fromList
    [ ("x", IntVal 3),
      ("a", ArrayVal [1, 2, 3, 4]),
      ("y", BoolVal True)
    ]

-- | Any store can be pretty-printed and displayed concisely using
-- | your pretty printers.

-- | We will be using the StateT transformer from the standard library
-- | to encode the type of our evaluator: it needs State to access the
-- | Store and wraps results in a Maybe to gracefully handle errors.
type Eval = StateT Store Maybe

-- |
-- We can use the name of a variable to find out its value
-- or update it in an assignment.
--
-- First, let's write a function that looks up values from the store. If
-- a variable doesn't exist, this function can error. Remember:
-- in regular Dafny variables must be initialized, but since we haven't implemented
-- those checks in MiniDafny, you can't assume here that they have already happened.
index :: Name -> Eval Value
index name = do
  vars <- get
  lift $ vars !? name

test_index :: Test
test_index =
  "index tests"
    ~: TestList
      [ -- The global variable "x" is unitialized (i.e. not present in the initial store)
        evalStateT (index "x") initialStore ~?= Nothing,
        -- But there is a value for "x" available in the extended store
        evalStateT (index "x") extendedStore ~?= Just (IntVal 3)
      ]

-- |
-- We can also update values in the store. If the variable name doesn't already
-- exist in the store, it should be added. Otherwise, it should modify
-- the store according to the new association.
update :: Name -> Value -> Eval ()
update name value = do
  vars <- get
  put (Map.insert name value vars)

test_update :: Test
test_update =
  "update tests"
    ~: TestList
      [ -- If we assign to x, then we can find its new value
        evalStateT (update "x" (IntVal 4) >> index "x") initialStore ~?= Just (IntVal 4),
        -- If we assign to x, then we can find its new value
        evalStateT (update "x" (IntVal 5) >> index "x") extendedStore ~?= Just (IntVal 5),
        -- If we assign to y, then we can't find a value for x
        evalStateT (update "y" (IntVal 5) >> index "x") initialStore ~?= Nothing
      ]

-- |
-- We will also need a way to update the values of arrays in the store:
-- This function takes the name of a variable (that should correspond to
-- an ArrayVal in the store), and two values i and v (that should both be integers),
-- and updates the i-th location of the array with the new value v.
updateNth :: Name -> Value -> Value -> Eval ()
updateNth name i v = do
  arr <- index name
  case (arr, i) of
    (ArrayVal arr, IntVal i) -> lift (ArrayVal <$> doUpdate arr i) >>= update name
    _ -> lift Nothing
  where
    doUpdate :: [Int] -> Int -> Maybe [Int]
    doUpdate [] i = Nothing
    doUpdate (x : xs) 0 = case v of
      IntVal v -> Just $ (v : xs)
      _ -> Nothing
    doUpdate (x : xs) i = (x :) <$> doUpdate xs (i - 1)

test_updateNth :: Test
test_updateNth =
  "updateNth tests"
    ~: TestList
      [ -- If we update the first (0-based) element of "a", then we can find its new value
        evalStateT (updateNth "a" (IntVal 0) (IntVal 42) >> index "a") extendedStore ~?= Just (ArrayVal [42, 2, 3, 4]),
        -- If we try to update a non-array, then we fail
        evalStateT (updateNth "x" (IntVal 0) (IntVal 42)) extendedStore ~?= Nothing,
        -- If we try to update an index out-of-bounds, then we fail
        evalStateT (updateNth "a" (IntVal 5) (IntVal 42)) extendedStore ~?= Nothing
      ]

test_store :: Test
test_store =
  "store tests"
    ~: TestList
      [ test_index,
        test_update,
        test_updateNth
      ]

-- | Expression Evaluator |
--   ------------------------
--
-- Your next job is to finish `evalE`, an evaluator for expressions.
-- This function should take as input an expression and return a
-- store-transformer that yields a `Value`. (See the type of `evalE` below.)
--
-- Now implement the rest of `evalE`, referring to the Dafny
-- to understand what the unary and binary operators should do. You may wish to define
-- helper functions as part of your implementation. (As a style check, you
-- should not use `evalStateT`, `execStateT`, or `runStateT` anywhere in
-- your definition of `evalE` or its helper functions.)
--
-- Your expression evaluator should also be *total*.  For any input it should
-- produce some value. However, we don't have exceptions (or typechecking!), so
-- if you don't know how to interpret an expression (such as `2 + true` or an
-- uninitialized variable) your code should return `Nothing`.

-- | Expression evaluator
evalE :: Expression -> Eval Value
evalE (Val v) = return v
evalE (Op2 e1 o e2) = do
  v1 <- evalE e1
  v2 <- evalE e2
  lift $ evalOp2 o v1 v2
evalE (Var (Name name)) = index name
evalE (Var (Proj name indExpr)) = do
  arrVal <- index name
  indVal <- evalE indExpr
  case (arrVal, indVal) of
    (ArrayVal arr, IntVal i) ->
      if i < length arr
        then lift $ Just $ IntVal (arr !! i)
        else lift Nothing
    _ -> lift Nothing
evalE (Op1 o e) = do
  v <- evalE e
  case (o, v) of
    (Neg, IntVal i) -> lift $ Just $ IntVal $ -i
    (Not, BoolVal b) -> lift $ Just $ BoolVal $ not b
    (Len, ArrayVal arr) -> lift $ Just $ IntVal $ length arr
    _ -> lift Nothing

evalOp2 :: Bop -> Value -> Value -> Maybe Value
evalOp2 Plus (IntVal i1) (IntVal i2) = Just $ IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = Just $ IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = Just $ IntVal (i1 * i2)
evalOp2 Divide (IntVal _) (IntVal 0) = Nothing
evalOp2 Divide (IntVal i1) (IntVal i2) = Just $ IntVal (i1 `div` i2)
evalOp2 Modulo (IntVal i1) (IntVal i2) = Just $ IntVal (i1 `mod` i2)
evalOp2 Eq v1 v2 = Just $ BoolVal $ v1 == v2
evalOp2 Neq v1 v2 = Just $ BoolVal $ v1 /= v2
evalOp2 Gt (IntVal i1) (IntVal i2) = Just $ BoolVal $ i1 > i2
evalOp2 Ge (IntVal i1) (IntVal i2) = Just $ BoolVal $ i1 >= i2
evalOp2 Lt (IntVal i1) (IntVal i2) = Just $ BoolVal $ i1 < i2
evalOp2 Le (IntVal i1) (IntVal i2) = Just $ BoolVal $ i1 <= i2
evalOp2 Conj (BoolVal b1) (BoolVal b2) = Just $ BoolVal $ b1 && b2
evalOp2 Disj (BoolVal b1) (BoolVal b2) = Just $ BoolVal $ b1 || b2
evalOp2 Implies (BoolVal b1) (BoolVal b2) = Just $ BoolVal $ not b1 || b2
evalOp2 Iff (BoolVal b1) (BoolVal b2) = Just $ BoolVal $ (b1 && b2) || (not b1 && not b2)
evalOp2 _ _ _ = Nothing

-- |
-- To test `evalE`, we can write a function that evaluates expressions with a
-- specified store using the `evalStateT` operation from the `State` monad
-- library.
evaluate :: Expression -> Store -> Maybe Value
evaluate e = evalStateT (evalE e)

-- |
--
-- Now would be a good time to add more unit test cases for your expression evaluator.
-- You should also make sure that your expression evaluation *always* returns a result,
-- even for "buggy" code. Your evaluator should never use "error" or trigger
-- any sort of runtime exception in Haskell.
--
-- (Complete) Statement Evaluator
-- ------------------------------
--
-- In this problem, you will need to implement an evaluator for
-- statements.  `evalS` should evaluate the given statement
-- completely, if possible. You may also implement a second evaluator
-- (`stepS`) that works step-by-step, evaluating only one piece at a time.
-- Although both evaluators are similar, the first one is a bit simpler. However, this
-- evaluator could go into an infinite loop if the MiniDafny program does not terminate.
-- In other words, you should *not* test this evaluator on the program `while true do ; end`.
eval :: Block -> Eval ()
eval (Block ss) = forM_ ss evalS

test_expr :: Test
test_expr = "expr eval tests" ~: TestList []

-- | Statement evaluator
evalS :: Statement -> Eval ()
evalS (Decl (name, typ) expr) = do
  v <- evalE expr
  let res = update name v
   in case (v, typ) of
        (IntVal _, TInt) -> res
        (BoolVal _, TBool) -> res
        (ArrayVal _, TArray TInt) -> res
        _ -> lift Nothing
evalS (Assert (Predicate pred)) = do
  v <- evalE pred
  case v of
    BoolVal True -> lift $ Just ()
    _ -> lift Nothing
evalS (Assign (Name name) expr) = do
  newVal <- evalE expr
  update name newVal
-- prevVal <- index name
-- let res = update name newVal
--  in case (prevVal, newVal) of
--       (IntVal _, IntVal _) -> res
--       (BoolVal _, BoolVal _) -> res
--       (ArrayVal _, ArrayVal _) -> res
--       _ -> lift Nothing
evalS (Assign (Proj name ind) expr) = do
  v <- evalE expr
  i <- evalE ind
  case v of
    IntVal _ -> updateNth name v i
    _ -> lift Nothing
evalS (If condExpr thenExpr elseExpr) = do
  cond <- evalE condExpr
  case cond of
    BoolVal True -> eval thenExpr
    BoolVal False -> eval elseExpr
    _ -> lift Nothing
evalS w@(While (Predicate invExpr) condExpr body) = do
  cond <- evalE condExpr
  case cond of
    BoolVal True -> do
      eval body
      inv <- evalE invExpr
      guard (inv == BoolVal True)
      evalS w
    BoolVal False -> lift $ Just ()
    _ -> lift Nothing
evalS Empty = lift $ Just ()

-- |
--
-- Don't forget that your evaluator should never call Haskell's "error" or
-- trigger a runtime exception.
--
-- The final step is to implement the evaluator for methods. For that, we simply need to
-- update an empty store with values for each of its parameters.
runMethod :: Method -> [Value] -> Eval ()
runMethod (Method f ins outs _ ss) vs = do
  guard (length ins == length vs)
  forM_ (zip ins vs) $ \((x, _), v) -> modify $ Map.insert x v
  eval ss

-- |
--
-- To test your evaluator, you can use the following function
exec :: Method -> [Value] -> Maybe Store
exec m vs = execStateT (runMethod m vs) initialStore

-- |
--
-- > -------------------------- Test cases for exec -----------------------------
--
-- You can test your evaluator using the sample programs defined in the `Syntax`
-- module.
--
-- However, if you run into bugs, you'll probably want to write some unit tests at this point.
test_simple_method =
  "simple method"
    ~: TestList
      [ exec
          ( Method
              "Foo"
              [("x", TInt), ("y", TInt)]
              [("res", TBool)]
              []
              (Block [Assign (Name "res") (Op2 (Var (Name "x")) Le (Var (Name "y")))])
          )
          [IntVal 4, IntVal 100]
          ~?= Just (Map.fromList [("x", IntVal 4), ("y", IntVal 100), ("res", BoolVal True)])
      ]

test_minmax =
  "minmax"
    ~: TestList
      [ exec wMinMax [IntVal 4, IntVal 3]
          ~?= Just (Map.fromList [("min", IntVal 3), ("max", IntVal 4), ("x", IntVal 4), ("y", IntVal 3)])
      ]

test_loopToZero =
  "loopToZero"
    ~: TestList
      [ exec wLoopToZero [IntVal 5, IntVal 15]
          ~?= Just (Map.fromList [("m",IntVal 5),("p",IntVal 15),("x",IntVal 0),("z",IntVal 10)])
      ]

testAll :: Test
testAll =
  TestList
    [ test_store,
      test_simple_method,
      test_minmax,
      test_loopToZero
    ]
