-- | A Parser for MiniDafny
--     ======================
--
-- For this problem, you will implement a parser for the Lu programming language.
module DafnyParser where

-- \|
--
-- Make sure that you read the [`Syntax`](Syntax.html) module that describes
-- the syntax of MiniDafny before continuing.
--
-- This problem also uses definitions from the Parsers module from the lecture
-- notes, gathered together in the module [`Parser.hs`](Parser.hs). Operations
-- such as `chainl1` and `filter` are imported as `P.chainl1` and `P.filter`.
-- You should also familiarize yourself with this module before continuing.
--
-- The goal of this part of the exercise is to give you practice with the
-- operations in the `Control.Applicative` library. As a result the `Parser`
-- type is *not* given a monad instance, so you will not be able use `do`
-- notation with it. Furthermore, you may not edit the `Parser` module, and you
-- do not have access to the constructor for the `Parser` type, so you will not
-- be able to define your own monad instance either.
--

-- import Control.Applicative

import Control.Monad (guard)
import Data.Char qualified as Char
import Data.Functor (($>))
import Printer
import Syntax
import System.IO qualified as IO
import System.IO.Error qualified as IO
import Test.HUnit (Assertion, Counts, Test (..), assert, assertEqual, runTestTT, (~:), (~?=))
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Error (Message (Message), newErrorMessage)
import Text.Parsec.Pos (initialPos)

type Parser = Parsec String ()

-- | Testing your Parser
--      ------------------
--
-- Your primary method of testing your parser should be using the following properties, though you will also
-- want to define your own unit tests as you go.
--
-- In particular, the following "round tripping" properties should be satisfied
-- by your implementation. These properties state that given an arbitrary
-- Value/Expression/Statement, if we pretty print it
prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = parse valueP "" (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = parse expP "" (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = parse statementP "" (pretty s) == Right s

-- | More Parser combinators
--     -----------------------
--
-- As a warm-up, let's define a few helper functions that we can use later.
--
-- In general, so that our parsers are flexible about spaces that appear in
-- source programs, all of the parsers will need to skip over any trailing white
-- space.
--
-- First, define a parser combinator which takes a parser, runs it,
-- then skips over any whitespace characters occurring afterwards. HINT: you'll
-- need the `space` parser from the [Parser](Parser.hs) library.
wsP :: Parser a -> Parser a
wsP p = p <* spaces

test_wsP :: Test
test_wsP =
  TestList
    [ parse (wsP letter) "" "a\n" ~?= Right 'a',
      parse (many (wsP letter)) "" "a b \n   \t c" ~?= Right "abc"
    ]

-- |
-- Use this to define a parser that accepts *only* a particular string `s`
-- and consumes any white space that follows. The last test case ensures
-- that trailing whitespace is being treated appropriately.
stringP :: String -> Parser ()
stringP s = wsP (string' s) $> ()

test_stringP :: Test
test_stringP =
  TestList
    [ parse (stringP "a") "" "a" ~?= Right (),
      -- parse (stringP "a") "" "b" ~?= Left "No parses", -- TODO update this test
      parse (many (stringP "a")) "" "a  a" ~?= Right [(), ()]
    ]

-- | Define a parser that will accept a particular string `s`, returning a
-- | given value `x`, and also and consume any white space that follows.
constP :: String -> a -> Parser a
constP s k = stringP s $> k

test_constP :: Test
test_constP =
  TestList
    [ parse (constP "&" 'a') "" "&  " ~?= Right 'a',
      parse (many (constP "&" 'a')) "" "&   &" ~?= Right "aa"
    ]

-- | We will also use `stringP` for some useful operations that parse between
-- | delimiters, consuming additional whitespace.
parens :: Parser a -> Parser a
parens = between (stringP "(") (stringP ")")

braces :: Parser a -> Parser a
braces = between (stringP "{") (stringP "}")

-- >>> parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]"
-- Right [1,1,1]
brackets :: Parser a -> Parser a
brackets = between (stringP "[") (stringP "]")

-- | Parsing Constants
--     -----------------
--
-- Now let's write parsers for the `Value` type, except for table constants
-- (which we won't parse).
valueP :: Parser Value
valueP = intValP <|> boolValP

-- | To do so, fill in the implementation of the four parsers above. As above, these
--   four parsers should consume any following whitespace. You can make sure that happens
--   by testing 'many' uses of the parser in a row.

-- >>> parse (many intValP) "1 2\n 3"
-- No instance for (Show (String -> Either ParseError [Value]))
--   arising from a use of `evalPrint'
--   (maybe you haven't applied a function to enough arguments?)
-- In a stmt of an interactive GHCi command: evalPrint it_aChK
intValP :: Parser Value
intValP = wsP $ fmap (IntVal . read) (many1 digit)

-- >>> parse (many boolValP) "true false\n true"
-- Right [BoolVal True,BoolVal False,BoolVal True]
boolValP :: Parser Value
boolValP = (keyword "true" $> BoolVal True) <|> (keyword "false" $> BoolVal False)

-- | At this point you should be able to run tests using the `prop_roundtrip_val` property.

-- | Parsing Types
--     -------------
--
-- We provide you with the parser for types, which for miniDafny can only be "int", "bool", or "array<int>".
typeP :: Parser Type
typeP =
  constP "int" TInt
    <|> constP "bool" TBool
    <|> stringP "array" *> stringP "<" *> typeP <* stringP ">"
    <|> fmap TNamed nameP

-- | Parsing Expressions
--     -------------------
--
-- Next, let's parse some Mini Dafny expressions.
--
-- We've already stratified the grammar for you, so that we'll get the
-- appropriate precedence and associativity for the binary and unary
-- operators. Make sure to read the end of the parsers lecture to understand how
-- this code works.
--
-- However, this code *won't* work until you complete all the parts of this section.
expP :: Parser Expression
expP = l1P
  where
    l1P = l2P `chainl1` opAtLevel 1
    l2P = l3P `chainl1` opAtLevel 2
    l3P = l4P `chainl1` opAtLevel 3
    l4P = l6P `chainl1` opAtLevel 4
    l6P = l7P `chainl1` opAtLevel 6
    l7P = uopexpP `chainl1` opAtLevel 7
    uopexpP =
      lhsP
        <|> Op1 <$> uopP <*> uopexpP
    lhsP = fmap (foldl (\obj fields -> LHSExpr $ Get obj fields)) baseP <*> many (stringP "." *> nameP)
    baseP =
      Val <$> valueP
        <|> parens expP
        <|> LHSExpr <$> varP

-- | Parse an operator at a specified precedence level
opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l =
  try
    ( do
        op <- bopP
        guard (level op == l)
        pure $ flip Op2 op
    )

op :: [(String, Bop)] -> Parser (Expression -> Expression -> Expression)
op ops = flip Op2 <$> choice [constP s bop | (s, bop) <- ops]

-- | A variable is a prefix followed by array indexing or ".Length" or just a name.
-- | We've also done this one for you.

-- >>>  parse (many varP) "x y z"
-- Right [Var "x", Var "y", Var "z"]
-- >>> parse varP "y[1]"
-- Right (Proj "y" (Val (IntVal 1)))
varP :: Parser LHSExpr
varP = Var <$> nameP

-- |
-- Define an expression parser for names. Names can be any sequence of upper and
-- lowercase letters, digits and underscores, not beginning with a digit and not
-- being a reserved word. Your parser should also consume any trailing
-- whitespace characters.
reserved :: [String]
reserved =
  [ "assert",
    "break",
    "else",
    "Length",
    "false",
    "for",
    "function",
    "invariant",
    "if",
    "in",
    "return",
    "true",
    "method",
    "int",
    "bool",
    "while",
    "requires",
    "ensures"
  ]

-- >>> parse (many nameP) "x sfds _ int"
-- Right ["x","sfds", "_"]
nameP :: Parser Name
nameP =
  let anyName =
        fmap (:) (choice [letter, char '_'])
          <*> many (choice [alphaNum, char '_'])
   in do
        name <- wsP anyName
        guard $ notElem name reserved
        return name

keyword :: String -> Parser ()
keyword word = wsP $ try (string' word *> notFollowedBy (alphaNum <|> char '_'))

-- Now write parsers for the unary and binary operators. Make sure you
--  check out the Syntax module for the list of all possible
--  operators. The tests are not exhaustive.

-- >>> parse (many uopP) "- - !"
-- Right [Neg,Neg,Not]
uopP :: Parser Uop
uopP = choice [constP "-" Neg, constP "!" Not]

-- >>> parse (many bopP) "+ >= &&"
-- Right [Plus,Ge,Conj]
bopP :: Parser Bop
bopP =
  choice
    [ constP "+" Plus,
      constP "-" Minus,
      constP "*" Times,
      constP "/" Divide,
      constP "%" Modulo,
      constP "!=" Neq,
      constP "==>" Implies,
      constP "<==>" Iff,
      constP "==" Eq,
      constP ">=" Ge,
      constP ">" Gt,
      constP "<=" Le,
      constP "<" Lt,
      constP "&&" Conj,
      constP "||" Disj
    ]

-- | At this point you should be able to test the  `prop_roundtrip_exp` property.

-- | Parsing Statements
--     ------------------
--
-- First, define a parser for bindings...
bindingP :: Parser Binding
bindingP = fmap (,) (nameP <* stringP ":") <*> typeP

-- | ...and predicates...
predicateP :: Parser Predicate
predicateP = fmap Predicate expP

-- | Finally, define a parser for statements:
statementP :: Parser Statement
statementP =
  choice
    [ fmap Decl (keyword "var" *> bindingP <* stringP ":=") <*> expP <* stringP ";",
      fmap Assert (keyword "assert" *> predicateP) <* stringP ";",
      fmap If (keyword "if" *> expP)
        <*> braces blockP
        <*> option (Block []) (keyword "else" *> braces blockP),
      fmap (flip While) (keyword "while" *> expP) <*> invariantP <*> braces blockP,
      assignStmtP
    ]

assignStmtP :: Parser Statement
assignStmtP = do
  expr <- expP
  case expr of
    LHSExpr lhs -> stringP ":=" *> (Assign lhs <$> expP) <* stringP ";"
    _ -> ExprStmt expr <$ stringP ";"

invariantP :: Parser Predicate
invariantP = option (Predicate (Val (BoolVal True))) (keyword "invariant" *> predicateP)

-- | ... and one for blocks.
blockP :: Parser Block
blockP = Block <$> many statementP

-- | Parsing Methods
--     ---------------
--
--   Implement parsing for methods. You will probably want to modularize it
--   by implementing parsing for specifications and many bindings.
methodP :: Parser Method
methodP =
  fmap
    Method
    (stringP "method" *> nameP)
    <*> inOutBindings
    <*> ((stringP "returns" *> inOutBindings) <|> pure [])
    <*> many specP
    <*> braces blockP

-- | Parse both parameter lists and return value lists
inOutBindings = parens $ sepBy bindingP (stringP ",")

specP :: Parser Specification
specP =
  choice
    [ stringP "requires" *> fmap Requires predicateP,
      stringP "ensures" *> fmap Ensures predicateP,
      stringP "modifies" *> fmap Modifies nameP
    ]

classP :: Parser ClassDef
classP =
  keyword "class"
    *> fmap ClassDef nameP
    <*> (stringP "{" *> many fieldP)
    <*> many methodP
    <* stringP "}"

fieldP :: Parser Binding
fieldP = keyword "var" *> bindingP

-- | Parsing Expressions and Files
--     -----------------------------
--
-- Finally, we'll export these convenience functions for calling
-- the parser.
parseDafnyExp :: String -> Either ParseError Expression
parseDafnyExp = parse expP ""

parseDafnyStat :: String -> Either ParseError Statement
parseDafnyStat = parse statementP ""

parseDafnyFile :: String -> IO (Either ParseError Method)
parseDafnyFile filename = do
  IO.catchIOError
    ( do
        handle <- IO.openFile filename IO.ReadMode
        str <- IO.hGetContents handle
        pure $ parse (const <$> methodP <*> eof) filename str
    )
    ( \e ->
        pure $ Left $ newErrorMessage (Message $ show e) (initialPos filename)
    )

{- File-based tests
   ----------------
-}

tParseFiles :: Test
tParseFiles =
  "parse files"
    ~: TestList
      [ -- "abs"  ~: p "dafny/abs.dfy"  wAbs,
        -- "minVal"  ~: p "dafny/findMinVal.dfy"  wMinVal,
        -- "minIndex"  ~: p "dafny/findMinIndex.dfy"  wMinIndex,
        -- "arraySpec" ~: p "dafny/arraySpec.dfy" wArraySpec,
        "minMax" ~: p "dafny/minMax.dfy" wMinMax
      ]
  where
    p fn ast = do
      result <- parseDafnyFile fn
      assertEqual (fn ++ " failed") (Right ast) result

-- | Unit Tests
--      ---------
--
-- These unit tests summarize the tests given above.
test_comb =
  "parsing combinators"
    ~: TestList
      [ parse (wsP letter) "" "a" ~?= Right 'a',
        parse (many (wsP letter)) "" "a b \n   \t c" ~?= Right "abc",
        parse (stringP "a") "" "a" ~?= Right (),
        -- parse (stringP "a") "" "b" ~?= Left "No parses", -- TODO update this test
        parse (many (stringP "a")) "" "a  a" ~?= Right [(), ()],
        parse (constP "&" 'a') "" "&  " ~?= Right 'a',
        parse (many (constP "&" 'a')) "" "&   &" ~?= Right "aa",
        parse (many (brackets (constP "1" 1))) "" "[1] [  1]   [1 ]" ~?= Right [1, 1, 1]
      ]

test_value =
  "parsing values"
    ~: TestList
      [ parse (many intValP) "" "1 2\n 3" ~?= Right [IntVal 1, IntVal 2, IntVal 3],
        parse (many boolValP) "" "true false\n true" ~?= Right [BoolVal True, BoolVal False, BoolVal True]
      ]

test_exp =
  "parsing expressions"
    ~: TestList
      [ parse (many varP) "" "x y z" ~?= Right [Var "x", Var "y", Var "z"],
        parse (many nameP) "" "x sfds _" ~?= Right ["x", "sfds", "_"],
        parse (many uopP) "" "- -" ~?= Right [Neg, Neg],
        parse (many bopP) "" "+ >= .." ~?= Right [Plus, Ge],
        parse expP "" "1" ~?= Right (Val (IntVal 1)),
        parse (opAtLevel (level Plus) $> ()) "" "+" ~?= Right (),
        parse expP "" "1 + 2" ~?= Right (Op2 (Val (IntVal 1)) Plus (Val (IntVal 2))),
        parse expP "" "(1).bar.baz" ~?= Right (LHSExpr (Get (LHSExpr (Get (Val (IntVal 1)) "bar")) "baz"))
      ]

test_stat =
  "parsing statements"
    ~: TestList
      [ parse statementP "" "x := 3;" ~?= Right (Assign (Var "x") (Val (IntVal 3))),
        parse statementP "" "2.foo := 3;" ~?= Right (Assign (Get (Val (IntVal 2)) "foo") (Val (IntVal 3))),
        parse statementP "" "if x { y := true; }"
          ~?= Right (If (LHSExpr (Var "x")) (Block [Assign (Var "y") (Val $ BoolVal True)]) (Block [])),
        parse statementP "" "while 0 { }"
          ~?= Right (While (Predicate (Val (BoolVal True))) (Val (IntVal 0)) (Block []))
      ]

test_class =
  "parsing classes"
    ~: TestList
      [ parse classP "" "class foo { var x: int method bar() {} }"
          ~?= Right (ClassDef "foo" [("x", TInt)] [Method "bar" [] [] [] (Block [])])
      ]

-- | Testing summary

--------------------

test_all :: Test
test_all = TestList [test_comb, test_value, test_exp, test_stat, test_class, tParseFiles]
