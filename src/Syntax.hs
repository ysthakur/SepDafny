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
data Type
  = TInt
  | TBool
  | TArray Type
  | TNamed Name
  deriving (Eq, Ord, Show)

-- | A struct definition. No type parameters for now
data StructDef = StructDef {structName :: Name, fields :: [Field]} deriving (Eq, Show)

data Field = Field {mutable :: Bool, fieldName :: Name, typ :: Type} deriving (Eq, Show)

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
  | Assign LHSExpr Expression -- x := e
  | If Expression Block Block -- if e { s1 } else { s2 }
  | While Predicate Expression Block -- while e invariant p { s }
  | ExprStmt Expression -- method call
  deriving (Eq, Show)

-- | Expressions are variables, literal constants, or operators applied
-- | to sub-expressions:
data Expression
  = LHSExpr LHSExpr -- Variables, indexing, field access
  | Val Value -- literal values
  | Op1 Uop Expression -- unary operators
  | Op2 Expression Bop Expression -- binary operators
  deriving (Eq, Ord, Show)

data LHSExpr
  = Var Name -- Variables
  | Get Expression Name -- Field access
  | Proj Expression Expression -- Indexing into arrays
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

-- | Test Programs |
--   =================
--
-- Below are some test programs that you can use in this assignment. These programs can also be
-- found in the corresponding files in the `dafny` folder. Please take a look at these files to
-- familiarize yourself with the concrete syntax of MiniDafny
var :: String -> Expression
var name = LHSExpr $ Var name

wMinMax =
  Method
    "MinMax"
    [("x", TInt), ("y", TInt)]
    [("min", TInt), ("max", TInt)]
    [Ensures (Predicate (Op2 (Op2 (Op2 (var "min") Le (var "x")) Conj (Op2 (var "min") Le (var "y"))) Conj (Op2 (Op2 (var "min") Eq (var "x")) Disj (Op2 (var "min") Eq (var "y"))))), Ensures (Predicate (Op2 (Op2 (Op2 (var "max") Ge (var "x")) Conj (Op2 (var "max") Ge (var "y"))) Conj (Op2 (Op2 (var "max") Eq (var "x")) Disj (Op2 (var "max") Eq (var "y")))))]
    ( Block
        [ If
            (Op2 (var "x") Lt (var "y"))
            ( Block
                [ Assign (Var "min") (var "x"),
                  Assign (Var "max") (var "y")
                ]
            )
            ( Block
                [ Assign (Var "max") (var "x"),
                  Assign (Var "min") (var "y")
                ]
            )
        ]
    )

wLoopToZero = Method "LoopToZero" [("m", TInt), ("p", TInt)] [("x", TInt), ("z", TInt)] [Requires (Predicate (Op2 (var "m") Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (var "z") Eq (Op2 (var "p") Minus (var "m"))))] (Block [Assign (Var "x") (var "m"), Assign (Var "z") (var "p"), While (Predicate (Op2 (Op2 (var "x") Ge (Val (IntVal 0))) Conj (Op2 (Op2 (var "z") Minus (var "x")) Eq (Op2 (var "p") Minus (var "m"))))) (Op2 (var "x") Gt (Val (IntVal 0))) (Block [Assign (Var "z") (Op2 (var "z") Minus (Val (IntVal 1))), Assign (Var "x") (Op2 (var "x") Minus (Val (IntVal 1)))])])

wTwoLoops = Method "TwoLoops" [("a", TInt), ("b", TInt), ("c", TInt)] [("x", TInt), ("y", TInt), ("z", TInt)] [Requires (Predicate (Op2 (Op2 (Op2 (var "a") Gt (Val (IntVal 0))) Conj (Op2 (var "b") Gt (Val (IntVal 0)))) Conj (Op2 (var "c") Gt (Val (IntVal 0))))), Ensures (Predicate (Op2 (var "z") Eq (Op2 (Op2 (var "a") Plus (var "b")) Plus (var "c"))))] (Block [Assign (Var "x") (Val (IntVal 0)), Assign (Var "y") (Val (IntVal 0)), Assign (Var "z") (var "c"), While (Predicate (Op2 (Op2 (Op2 (var "x") Le (var "a")) Conj (Op2 (var "y") Eq (Val (IntVal 0)))) Conj (Op2 (var "z") Eq (Op2 (Op2 (var "x") Plus (var "y")) Plus (var "c"))))) (Op2 (var "x") Lt (var "a")) (Block [Assign (Var "x") (Op2 (var "x") Plus (Val (IntVal 1))), Assign (Var "z") (Op2 (var "z") Plus (Val (IntVal 1)))]), While (Predicate (Op2 (Op2 (Op2 (var "y") Le (var "b")) Conj (Op2 (var "x") Eq (var "a"))) Conj (Op2 (var "z") Eq (Op2 (Op2 (var "a") Plus (var "y")) Plus (var "c"))))) (Op2 (var "y") Lt (var "b")) (Block [Assign (Var "y") (Op2 (var "y") Plus (Val (IntVal 1))), Assign (Var "z") (Op2 (var "z") Plus (Val (IntVal 1)))])])

wSquare = Method "Square" [("x", TInt)] [("z", TInt)] [Requires (Predicate (Op2 (var "x") Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (var "z") Eq (Op2 (var "x") Times (var "x"))))] (Block [Decl ("y", TInt) (Val (IntVal 0)), Assign (Var "z") (Val (IntVal 0)), While (Predicate (Op2 (Op2 (var "y") Le (var "x")) Conj (Op2 (var "z") Eq (Op2 (var "y") Times (var "x"))))) (Op2 (var "y") Lt (var "x")) (Block [Assign (Var "z") (Op2 (var "z") Plus (var "x")), Assign (Var "y") (Op2 (var "y") Plus (Val (IntVal 1)))])])

wSquareRoot = Method "SquareRoot" [("x", TInt)] [("z", TInt)] [Requires (Predicate (Op2 (var "x") Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (Op2 (Op2 (var "z") Times (var "z")) Le (var "x")) Conj (Op2 (var "x") Lt (Op2 (Op2 (var "z") Plus (Val (IntVal 1))) Times (Op2 (var "z") Plus (Val (IntVal 1)))))))] (Block [Assign (Var "z") (Val (IntVal 0)), While (Predicate (Op2 (Op2 (var "z") Times (var "z")) Le (var "x"))) (Op2 (Op2 (Op2 (var "z") Plus (Val (IntVal 1))) Times (Op2 (var "z") Plus (Val (IntVal 1)))) Le (var "x")) (Block [Assign (Var "z") (Op2 (var "z") Plus (Val (IntVal 1)))])])

wIntDiv = Method "IntDiv" [("m", TInt), ("n", TInt)] [("d", TInt), ("r", TInt)] [Requires (Predicate (Op2 (var "n") Gt (Val (IntVal 0)))), Ensures (Predicate (Op2 (var "m") Eq (Op2 (Op2 (var "d") Times (var "n")) Plus (var "r")))), Ensures (Predicate (Op2 (Op2 (Val (IntVal 0)) Le (var "r")) Conj (Op2 (var "r") Lt (var "n"))))] (Block [Assign (Var "d") (Op2 (var "m") Divide (var "n")), Assign (Var "r") (Op2 (var "m") Modulo (var "n"))])
