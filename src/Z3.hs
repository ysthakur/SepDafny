-- | Z3 integration |
--   ==================
--
--   The final step in implementing a verifier like Dafny is to
--   check whether the verification conditions generated using
--   weakest preconditions actually hold. To do that, we will
--   use the Z3 theorem prover.
--
--   As discussed in class on Thursday (4/18 -- recording available),
--   we will do this by creating a so called "SMTLib" file with the
--   extnension .smt2 for _every_ verification condition.
--
--   For an example, consider the first verification condition of our
--   "Square.dfy" program:
--
--     x > 0 && true ==> (0 <= x && 0 == 0 * x)
--
--   This gives rise to the following .smt2 file (available as
--   "Square.dfy1.smt2") on the course website.
--
-- ; Declare Constant x
-- (declare-const x Int)
-- ; assert the negation of the verification condition:
-- (assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
-- ; ask z3 to check it
-- (check-sat)
--
--    Read below for additional details on the SMT2 format.
--
--    Your task is to create such a file given a Predicate p. We provide
--    you with a simple IO handler that relies on a function
--
--      toSMT :: Predicate -> String
--
--    Your final project is to implement this function.  To implement
--    this function, we have imported the pretty printing library we
--    used in a previous homework. It is highly recommended that you
--    mimic the organization of your pretty printers to facilitate
--    debugging your code.  That said, you are welcome to use any part
--    of the standard library that doesn't require editing the cabal
--    file of the project.
--
-- ========================
-- Declaration of Constants
-- ========================
--
--    The first part of the file is a series of constant declarations with
--    the following syntax:
--
-- (declare-const <variable-name> <type>)
--
--    Variable names are just strings, and for the purposes of this final
--    project, you can assume that all variables that appear in a predicate
--    are integers. To lift that assumption we would need to implement a type
--    checker for Dafny, which we haven't done.
--
--    Before you begin constructing the .smt2 file, you should calculate
--    the variables that appear in a given predicate p, and create a
--    declaration such as the one in the example for each one. We have
--    imported the Data.Set library for you --- it is recommended that
--    you use it, but again, you are welcome to design and implement
--    this final project in any way you see fit.
--
--
-- ==========
-- Assertions
-- ==========
--
--    The second part of the file is the negation of the verification condition
--    where every operation is in prefix form. For example, given the predicate:
--
--      (x > 0 && true) ==> (0 <= x && 0 == 0 * x)
--
--    we will assert it's negation:
--
--      (assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
--
--    Each operation appears in parentheses before its arguments:
--    For example:
--
--           x > 0              translates to              (> x 0)
--           0 * x              translates to              (* 0 x)
--       false && true          translates to              (and false true)
--           0 == x             translates to              (= 0 x)
--
--    While this format makes for syntax that is hard for humans to
--    read, you should find that it's much more suitable for being
--    automatically generated recursively from the AST of an expression.
--
-- =========
-- Check SAT
-- =========
--
--    As discussed in class, the final part of your file should be a single
--    call to check the satisfiability of the assertion you created above:
--
-- (check-sat)
--
--    Z3 (and similar solvers) are capable of finding satisfying assignments
--    for a plethora of formulas involving integer arithmetic, or returning
--    "unsat" if such an assignment doesn't exist. That's why we check for
--    the satisfiability of the negation of the verification condition: if
--    z3 says that the negation cannot be satisfied, then we are guaranteed
--    that it is a tautology that holds in all contexts.
module Z3 where

import Data.List (intersperse)
import Data.Set (Set)
import Data.Set qualified as Set
import Syntax
import System.Process (readProcessWithExitCode)
import Text.PrettyPrint (Doc, ($+$), (<+>))
import Text.PrettyPrint qualified as PP

-- | This is the function you need to implement. You can ignore arrays, as with
--   the weakest precondition homework, but everything else needs to be handled!
toSMT :: Predicate -> String
toSMT (Predicate p) =
  let vars = getVars p
   in PP.render
        ( PP.vcat (map (\v -> PP.parens (PP.text "declare-const" <+> PP.text v <+> PP.text "Int")) vars)
            $+$ PP.parens (PP.text "assert" <+> pp (Op1 Not p))
            $+$ PP.text "(check-sat)"
        )

getVars :: Expression -> [String]
getVars (Val val) = []
getVars (Op1 op e) = getVars e
getVars (Op2 lhs op rhs) =
  let leftVars = getVars lhs
   in let rightVars = getVars rhs in leftVars ++ filter (`notElem` leftVars) rightVars
getVars (LHSExpr (Var n)) = [n]
getVars (LHSExpr (Proj _ _)) = undefined
getVars (LHSExpr (Get _ _)) = undefined

class PP a where
  pp :: a -> Doc

instance PP Value where
  pp (IntVal i) = PP.int i
  pp (BoolVal b) = if b then PP.text "true" else PP.text "false"
  pp (ArrayVal l) = undefined

instance PP Uop where
  pp Neg = PP.char '-'
  pp Not = PP.text "not"
  pp Len = undefined

instance PP Bop where
  pp Plus = PP.char '+'
  pp Minus = PP.char '-'
  pp Times = PP.char '*'
  pp Divide = PP.text "div"
  pp Modulo = PP.text "mod"
  pp Eq = PP.char '='
  pp Neq = PP.text "distinct"
  pp Gt = PP.char '>'
  pp Ge = PP.text ">="
  pp Lt = PP.char '<'
  pp Le = PP.text "<="
  pp Conj = PP.text "and"
  pp Disj = PP.text "or"
  pp Implies = PP.text "=>"
  pp Iff = PP.char '='

instance PP Expression where
  pp (LHSExpr e) = pp e
  pp (Val v) = pp v
  pp (Op1 op e) = PP.parens (pp op <+> pp e)
  pp (Op2 lhs op rhs) = PP.parens (pp op <+> pp lhs <+> pp rhs)

instance PP LHSExpr where
  pp (Var n) = PP.text n
  pp (Proj _ _) = undefined
  pp (Get _ _) = undefined

-- | The name of the z3 executable. Change this to whatever it is in your system:
--   In unix based systems, this is just "z3".
--   In Windows, it will be the name of the executable that was installed alongside Dafny.
z3 :: String
z3 = "z3"

-- | This function uses "toSMT" in order to write a file, and invoke z3 on it, checking its
--   output. You're welcome to modify this function as you see fit, the only thing we will
--   automatically test is your "toSMT" function.
convertAndCheck :: Predicate -> String -> IO Bool
convertAndCheck p fn = do
  writeFile fn (toSMT p)
  (_exitCode, stdout, _stderr) <- readProcessWithExitCode z3 [fn] ""
  case stdout of
    's' : 'a' : 't' : _ -> return False
    'u' : 'n' : 's' : 'a' : 't' : _ -> return True
    _ -> error $ "Z3 output was neither sat or unsat: " ++ stdout
