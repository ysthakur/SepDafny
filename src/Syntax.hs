-- | Mini Dafny - Syntax |
--   -----------------------
--
-- This module defines data structures to represent the syntax of the "miniDafny" programming language.
-- You should read this file carefully to understand the miniDafny language, but you do not need to
-- edit this file.
--
-- This module contains:
--
-- 1. The definitions of the datatypes that represent the abstract syntax of miniDafny
-- 2. Sample programs written in miniDafny
module Syntax where

import Control.Monad (mapM_)
import Data.Char qualified as Char
import Data.List (intersperse)
import Data.Map (Map)
import Data.Map qualified as Map
import Test.HUnit

-- |
-- What is a miniDafny Program?
-- =====================
--
-- The general idea is that miniDafny is a very, very cut down version of the Dafny
-- verification language.
--
-- A program is a single Method with a name, a list of input variables,
-- a list of output variables, a sequence of requires/ensures/modifies
-- statements, followed by a main body.
data Method = Method Name [Binding] [Binding] [Specification] Block
  deriving (Eq, Show)

-- | A Name is just a type synonym for a String:
type Name = String -- either the name of a variable or the name of a method

-- | A Binding is a Name together with its Type:
type Binding = (Name, Type)

-- | For simplicity, types in miniDafny can be integers, booleans, or arrays of integers.
data Type = TInt | TBool | TArrayInt
  deriving (Eq, Ord, Show)

-- | Specifications are logical statements that describe program behaviors.
-- | They can be requires, ensures or modifies statements.
data Specification
  = Requires Predicate
  | Ensures Predicate
  | Modifies Name
  deriving (Eq, Show)

-- | A Predicate is a forall-quantified boolean formula, potentially with a precondition:

-- CHANGE: Bindings are removed. Predicates are now just (boolean) expressions.
-- data Predicate = Predicate [Binding] Expression
newtype Predicate = Predicate Expression
  deriving (Eq, Show)

-- | Programs are sequences of statements in a block:
newtype Block = Block [Statement] -- s1 ... sn
  deriving (Eq, Show)

-- | For convenience, we create these instances to join blocks together:
instance Semigroup Block where
  (<>) :: Block -> Block -> Block
  Block s1 <> Block s2 = Block (s1 <> s2)

instance Monoid Block where
  mempty :: Block
  mempty = Block []

-- | Statements themselves have the following forms:

-- CHANGE: While loops now have a single invariant
data Statement
  = Decl Binding Expression -- var x : int := e;
  | Assert Predicate -- assert p
  | Assign Var Expression -- x := e
  | If Expression Block Block -- if e { s1 } else { s2 }
  | While Predicate Expression Block -- while e invariant p { s }
  | Empty --
  deriving (Eq, Show)

-- | Expressions are variables, literal constants, or operators applied
-- | to sub-expressions:
data Expression
  = Var Var -- global variables x and array indexing
  | Val Value -- literal values
  | Op1 Uop Expression -- unary operators
  | Op2 Expression Bop Expression -- binary operators
  deriving (Eq, Ord, Show)

-- | The literal values include ints, booleans, and a special value for
--     arrays that should not appear directly in source programs, but is
--     used by the interpreter.
data Value
  = IntVal Int -- 1
  | BoolVal Bool -- false, true
  | ArrayVal [Int]
  deriving (Eq, Show, Ord)

-- | Unary operators are single argument functions: arithmetic negation, logical not, and a
-- | length operation for arrays.
data Uop
  = Neg -- `-` :: Int -> Int
  | Not -- `!` :: a -> Bool
  | Len -- `.Length` :: Table -> Int
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Binary operators are two-argument functions: arithmetic and comparison operators for
-- | integer values, and boolean connectives for boolean values.
data Bop
  = Plus -- `+`  :: Int -> Int -> Int
  | Minus -- `-`  :: Int -> Int -> Int
  | Times -- `*`  :: Int -> Int -> Int
  | Divide -- `/`  :: Int -> Int -> Int   -- floor division
  | Modulo -- `%`  :: Int -> Int -> Int   -- modulo
  | Eq -- `==` :: Int -> Int -> Bool
  | Neq -- `!=` :: Int -> Int -> Bool>
  | Gt -- `>`  :: Int -> Int -> Bool
  | Ge -- `>=` :: Int -> Int -> Bool
  | Lt -- `<`  :: Int -> Int -> Bool
  | Le -- `<=` :: Int -> Int -> Bool
  | Conj -- `&&` :: Bool -> Bool -> Bool
  | Disj -- `||` :: Bool -> Bool -> Bool
  | Implies -- `==>` :: Bool -> Bool -> Bool
  | Iff -- `<==>` :: Bool -> Bool -> Bool
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Variables and Arrays |
--   ------------------------
--
-- Variables are places that store values.
--
-- Arrays of integers are a primitive part of the language. They are data
-- structure that can be accessed by looking up the value associated
-- with an integer key, in a variable expression
--
--    t[1]    -- any integer value can be used as a key
--
-- or modified by introducing a new value associated with a key, using an
-- assignment statement:
--
--    t[1] = 3      -- any integer value can be stored in a table
--
-- We represent these globals and table fields, using the
-- following datatype definitions.
data Var
  = Name Name -- x, global variable
  | Proj Name Expression -- a[1], access array table using an integer
  deriving (Eq, Ord, Show)

-- | Test Programs |
--   =================
--
-- Below are some test programs that you can use in this assignment. These programs can also be
-- found in the corresponding files in the `dafny` folder. Please take a look at these files to
-- familiarize yourself with the concrete syntax of MiniDafny
wMinMax =
  Method
    "MinMax"
    [("x", TInt), ("y", TInt)]
    [("min", TInt), ("max", TInt)]
    [Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "min")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "min")) Le (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "min")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "min")) Eq (Var (Name "y")))))), Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "max")) Ge (Var (Name "x"))) Conj (Op2 (Var (Name "max")) Ge (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "max")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "max")) Eq (Var (Name "y"))))))]
    ( Block
        [ If
            (Op2 (Var (Name "x")) Lt (Var (Name "y")))
            ( Block
                [ Assign (Name "min") (Var (Name "x")),
                  Empty,
                  Assign (Name "max") (Var (Name "y")),
                  Empty
                ]
            )
            ( Block
                [ Assign (Name "max") (Var (Name "x")),
                  Empty,
                  Assign (Name "min") (Var (Name "y")),
                  Empty
                ]
            )
        ]
    )

wLoopToZero = Method "LoopToZero" [("m", TInt), ("p", TInt)] [("x", TInt), ("z", TInt)] [Requires (Predicate (Op2 (Var (Name "m")) Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "p")) Minus (Var (Name "m")))))] (Block [Assign (Name "x") (Var (Name "m")), Empty, Assign (Name "z") (Var (Name "p")), Empty, While (Predicate (Op2 (Op2 (Var (Name "x")) Ge (Val (IntVal 0))) Conj (Op2 (Op2 (Var (Name "z")) Minus (Var (Name "x"))) Eq (Op2 (Var (Name "p")) Minus (Var (Name "m")))))) (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Minus (Val (IntVal 1))), Empty, Assign (Name "x") (Op2 (Var (Name "x")) Minus (Val (IntVal 1))), Empty])])

wTwoLoops = Method "TwoLoops" [("a", TInt), ("b", TInt), ("c", TInt)] [("x", TInt), ("y", TInt), ("z", TInt)] [Requires (Predicate (Op2 (Op2 (Op2 (Var (Name "a")) Gt (Val (IntVal 0))) Conj (Op2 (Var (Name "b")) Gt (Val (IntVal 0)))) Conj (Op2 (Var (Name "c")) Gt (Val (IntVal 0))))), Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "b"))) Plus (Var (Name "c")))))] (Block [Assign (Name "x") (Val (IntVal 0)), Empty, Assign (Name "y") (Val (IntVal 0)), Empty, Assign (Name "z") (Var (Name "c")), Empty, While (Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Le (Var (Name "a"))) Conj (Op2 (Var (Name "y")) Eq (Val (IntVal 0)))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Plus (Var (Name "c")))))) (Op2 (Var (Name "x")) Lt (Var (Name "a"))) (Block [Assign (Name "x") (Op2 (Var (Name "x")) Plus (Val (IntVal 1))), Empty, Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))), Empty]), While (Predicate (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c")))))) (Op2 (Var (Name "y")) Lt (Var (Name "b"))) (Block [Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))), Empty, Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))), Empty])])

wSquare = Method "Square" [("x", TInt)] [("z", TInt)] [Requires (Predicate (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))] (Block [Decl ("y", TInt) (Val (IntVal 0)), Empty, Assign (Name "z") (Val (IntVal 0)), Empty, While (Predicate (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) (Op2 (Var (Name "y")) Lt (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x"))), Empty, Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))), Empty])])

wSquareRoot = Method "SquareRoot" [("x", TInt)] [("z", TInt)] [Requires (Predicate (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "z")) Times (Var (Name "z"))) Le (Var (Name "x"))) Conj (Op2 (Var (Name "x")) Lt (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Times (Op2 (Var (Name "z")) Plus (Val (IntVal 1)))))))] (Block [Assign (Name "z") (Val (IntVal 0)), Empty, While (Predicate (Op2 (Op2 (Var (Name "z")) Times (Var (Name "z"))) Le (Var (Name "x")))) (Op2 (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Times (Op2 (Var (Name "z")) Plus (Val (IntVal 1)))) Le (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))), Empty])])

wIntDiv = Method "IntDiv" [("m", TInt), ("n", TInt)] [("d", TInt), ("r", TInt)] [Requires (Predicate (Op2 (Var (Name "n")) Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (Var (Name "m")) Eq (Op2 (Op2 (Var (Name "d")) Times (Var (Name "n"))) Plus (Var (Name "r"))))), Ensures (Predicate (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "r"))) Conj (Op2 (Var (Name "r")) Lt (Var (Name "n")))))] (Block [Assign (Name "d") (Op2 (Var (Name "m")) Divide (Var (Name "n"))), Empty, Assign (Name "r") (Op2 (Var (Name "m")) Modulo (Var (Name "n"))), Empty])
