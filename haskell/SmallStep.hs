-- ReadMe:
--
-- This is Holly Casaletto's (hcasalet@ucsc.edu, 1707550) homework 4. In this homework I implemented
-- the small step semantics interpreter for PL WHILE using Haskell. For homework 1, 2, and 4, I have
-- used 3 diffrent programming languages, namely Java for homework 1, Python for homework 2, and Haskell
-- for homework 4.
--
-- Data structure:
-- Arithmetic Expression AExp, which has 6 cases as follows:
     -- ConstInt: evaluates to integer
     -- Var:      evaluates to the integer value the variable holds in the state store.
     -- Add:      evaluates to the sum of the two AExps to its left and right.
     -- Mul:      evaluates to the product of the two AExps to its left and right.
     -- Mns:      evaluates to the difference subtracting the 2nd AExp from the 1st AExp.
     -- Div:      evaluates to the quotient dividing the 1st AExp by the 2nd AExp.
-- Boolean Expression BEXP, which has 7 cases as follows:
     -- ConstBln: evaluates to either True or False
     -- Eql:      evaluates to True of AExp to its left equals to the one on its right; otherwise False.
     -- Les:      evaluates to True if its 1st AExp is less than its 2nd AExp; otherwise False.
     -- Grt:      evaluates to True if its 1st AExp is greater than its 2nd AExp; otherwise False.
     -- Ngt:      evaluates to True if the BExp is False; to False if it is True.
     -- And:      evaluates as the logical AND for its 1st and 2nd arguments.
     -- Orr:      evaluates to the logical OR for its 2st and 2nd arguments.
-- Command Expression Cmd, which has the following types:
     -- Asg x n:  assigns value n to variable x.
     -- Seq c d:  executes commands c and d sequentially.
     -- Cnd b c d: if b is true, execute c; else execute d
     -- Whl b c:  while b do c
     -- SKp:      follows the rule of skip and do nothing.
-- Functions:
     -- evali :: AExp -> Store -> Int: evaluates an arithmetic expression
     -- evalb :: BExp -> Store -> Bool: evaluates a boolean expression
     -- reduce :: Cmd -> Store -> (Cmd, Store): evaluates one step (small step) of the AST
     -- prtstate :: Store -> String: prints out the content of the state store
     -- showtupleitems :: [(String, Int)] -> [String]: help function for function prtstate.
     -- eval :: Cmd -> Store -> (): evaluates an AST recursively. Printing of each step and the
     --        store is called in this function.
-- Test cases:
--   5 test cases were tested. Test results attached here in this section:
--
-- Case 1: (x:=3;y:=5;)z:=11 -- [testing Seq, Assign]
-- ast1 = Seq (Seq (Asg "x" (ConstInt 3)) (Asg "y" (ConstInt 5))) (Asg "z" (ConstInt 11))
-- *Smallstep> eval ast1 s1
-- <x := 3; y := 5; z := 11,{}> ->
-- <skip; y := 5; z := 11,{x:3}> ->
-- <y := 5; z := 11,{x:3}> ->
-- <skip; z := 11,{x:3, y:5}> ->
-- <z := 11,{x:3, y:5}> ->
-- <skip,{x:3, y:5, z:11}> ->
--
-- Case 2: x:=1;y:=5;if !(x==y) then x:=y; else y:=x -- [if-true case]
-- ast2 = Seq (Seq (Asg "x" (ConstInt 1)) (Asg "y" (ConstInt 5))) (Cnd (Ngt (Eql (Var "x") (Var "y")))
--  (Asg "x" (Var "y")) (Asg "y" (Var "x")))
-- *Smallstep> eval ast2 s2
-- <x := 1; y := 5; if !(x == y) then x := y else y := x,{}> ->
-- <skip; y := 5; if !(x == y) then x := y else y := x,{x:1}> ->
-- <y := 5; if !(x == y) then x := y else y := x,{x:1}> ->
-- <skip; if !(x == y) then x := y else y := x,{x:1, y:5}> ->
-- <if !(x == y) then x := y else y := x,{x:1, y:5}> ->
-- <x := y,{x:1, y:5}> ->
-- <skip,{x:5, y:5}> ->
--
-- case 3: x:=0;if (x>0) x:=x-1; else x:=x+1 -- [if-false case]
-- ast3 = Seq (Asg "x" (ConstInt 0)) (Cnd (Grt (Var "x") (ConstInt 0)) (Asg "x" (Mns (Var "x")
--  (ConstInt 1))) (Asg "x" (Add (Var "x") (ConstInt 1))))
-- *Smallstep> eval ast3 s3
-- <x := 0; if x > 0 then x := x-1 else x := x+1,{}> ->
-- <skip; if x > 0 then x := x-1 else x := x+1,{x:0}> ->
-- <if x > 0 then x := x-1 else x := x+1,{x:0}> ->
-- <x := x+1,{x:0}> ->
-- <skip,{x:1}> ->
--
-- case 4: x:=0;while (x<5) x:=x+1 -- [while-true case]
-- ast4 = Seq (Asg "x" (ConstInt 0)) (Whl (Les (Var "x") (ConstInt 5)) (Asg "x" (Add (Var "x")
--  (ConstInt 1))))
-- *Smallstep> eval ast4 s4
-- <x := 0; while x < 5 do x := x+1,{}> ->
-- <skip; while x < 5 do x := x+1,{x:0}> ->
-- <while x < 5 do x := x+1,{x:0}> ->
-- <x := x+1; while x < 5 do x := x+1,{x:0}> ->
-- <skip; while x < 5 do x := x+1,{x:1}> ->
-- <while x < 5 do x := x+1,{x:1}> ->
-- <x := x+1; while x < 5 do x := x+1,{x:1}> ->
-- <skip; while x < 5 do x := x+1,{x:2}> ->
-- <while x < 5 do x := x+1,{x:2}> ->
-- <x := x+1; while x < 5 do x := x+1,{x:2}> ->
-- <skip; while x < 5 do x := x+1,{x:3}> ->
-- <while x < 5 do x := x+1,{x:3}> ->
-- <x := x+1; while x < 5 do x := x+1,{x:3}> ->
-- <skip; while x < 5 do x := x+1,{x:4}> ->
-- <while x < 5 do x := x+1,{x:4}> ->
-- <x := x+1; while x < 5 do x := x+1,{x:4}> ->
-- <skip; while x < 5 do x := x+1,{x:5}> ->
-- <while x < 5 do x := x+1,{x:5}> ->
-- <skip,{x:5}> ->
--
-- case 5: x:=6;while (x<5) x:=x-1 -- [while-false case]
-- ast5 = Seq (Asg "x" (ConstInt 6)) (Whl (Les (Var "x") (ConstInt 5)) (Asg "x" (Mns (Var "x")
--  (ConstInt 1))))
-- *Smallstep> eval ast5 s5
-- <x := 6; while x < 5 do x := x-1,{}> ->
-- <skip; while x < 5 do x := x-1,{x:6}> ->
-- <while x < 5 do x := x-1,{x:6}> ->
-- <skip,{x:6}> ->
--

module Smallstep where
import qualified Data.Map as Map
import Debug.Trace
import Data.List

type Store = Map.Map String Int
s = Map.empty

data AExp =  ConstInt Int
           | Var String
           | Add AExp AExp
           | Mul AExp AExp
           | Mns AExp AExp
           | Div AExp AExp
           deriving Eq

type State = [(String, Int)]

instance Show AExp where
   show (ConstInt n) = show n
   show (Var r)      = r
   show (Add x y)    = (show x) ++ "+" ++ (show y)
   show (Mul x y)    = (show x) ++ "*" ++ (show y)
   show (Mns x y)    = (show x) ++ "-" ++ (show y)
   show (Div x y)    = (show x) ++ "/" ++ (show y)

evali :: AExp -> Store ->  Int
evali aexp s = case aexp of
               ConstInt n -> n
               Add x y    ->  (evali x s) + (evali y s)
               Mul x y    ->  (evali x s) *  (evali y s)
               Mns x y    ->  (evali x s) -  (evali y s)
               Div x y    ->  (evali x s) `div` (evali y s)
               Var r      ->  s Map.! r

data BExp =  ConstBln Bool
           | Eql AExp AExp
           | Les AExp AExp
           | Grt AExp AExp
           | Ngt BExp
           | And BExp BExp
           | Orr BExp BExp
           deriving Eq

instance Show BExp where
   show (ConstBln b) = show b
   show (Eql x y)    = (show x) ++ " == " ++ (show y)
   show (Les x y)    = (show x) ++ " < " ++ (show y)
   show (Grt x y)    = (show x) ++ " > "  ++ (show y)
   show (Ngt b)      = "!(" ++ (show b) ++ ")"
   show (And a b)    = (show a) ++ " && " ++ (show b)
   show (Orr a b)    = (show a) ++ " || " ++ (show b)

evalb :: BExp -> Store -> Bool
evalb bexp s = case bexp of
               ConstBln b -> b
               Eql x y    -> (evali x s) == (evali y s)
               Les x y    -> (evali x s) < (evali y s)
               Grt x y    -> (evali x s) > (evali y s)
               Ngt b      ->  not (evalb b s)
               And a b    -> (evalb a s) && (evalb b s)
               Orr a b    -> (evalb a s) || (evalb b s)

data Void

data Cmd =  Asg String AExp
          | Seq Cmd Cmd
          | Cnd BExp Cmd Cmd
          | Whl BExp Cmd
          | Skp
          | None
          deriving Eq

instance Show Cmd where
   show (Asg x v)   = x ++ " := " ++ (show v)
   show (Seq c d)   = (show c) ++ "; " ++ (show d)
   show (Cnd b c d) = "if " ++ (show b) ++ " then " ++ (show c) ++ " else " ++ (show d)
   show (Whl b c)   = "while " ++ (show b) ++ " do " ++ (show c)
   show Skp         = "skip"
   show None        = ""

reduce :: Cmd -> Store -> (Cmd, Store)
reduce cmd s = case cmd of
               Asg x v    -> (Skp, Map.insert x (evali v s) s)
               Seq c d    -> if c == Skp then (d, s)
                             else do
                               let (c', s') = reduce c s
                               ((Seq c' d), s')
               Cnd b c d  -> if (evalb b s) then (c, s)
                             else (d, s)
               Whl b c    -> if (evalb b s) then ((Seq c cmd), s)
                             else (Skp, s)
               Skp        -> (None, s)

showtupleitems :: [(String, Int)] -> [String]
showtupleitems x = [(fst a) ++ ":" ++ (show (snd a))|a<-x]

prtstore :: Store -> String
prtstore s = "{" ++ (intercalate ", " (showtupleitems (Map.assocs s))) ++ "}"

eval :: Cmd -> Store -> ()
eval cmd s = trace ("<" ++ (show cmd) ++ "," ++ (prtstore s) ++ "> ->") $ do
             let (cmd', s') = reduce cmd s
             if cmd' /= None then (eval cmd' s')
             else ()

--------------
-- test cases:
--------------
-- case 1: (x:=3;y:=5;)z:=11 -- [testing Seq, Assign]
s1 = Map.empty
ast1 = Seq (Seq (Asg "x" (ConstInt 3)) (Asg "y" (ConstInt 5))) (Asg "z" (ConstInt 11))

-- case 2: x:=1;y:=5;if !(x==y) then x:=y; else y:=x -- [if-true case]
s2 = Map.empty
ast2 = Seq (Seq (Asg "x" (ConstInt 1)) (Asg "y" (ConstInt 5))) (Cnd (Ngt (Eql (Var "x") (Var "y"))) (Asg "x" (Var "y")) (Asg "y" (Var "x")))

-- case 3: x:=0;if (x>0) x:=x-1; else x:=x+1 -- [if-false case]
s3 = Map.empty
ast3 = Seq (Asg "x" (ConstInt 0)) (Cnd (Grt (Var "x") (ConstInt 0)) (Asg "x" (Mns (Var "x") (ConstInt 1))) (Asg "x" (Add (Var "x") (ConstInt 1))))

-- case 4: x:=0;while (x<5) x:=x+1 -- [while-true case]
s4 = Map.empty
ast4 = Seq (Asg "x" (ConstInt 0)) (Whl (Les (Var "x") (ConstInt 5)) (Asg "x" (Add (Var "x") (ConstInt 1))))

-- case 5: x:=6;while (x<5) x:=x-1 -- [while-false case]
s5 = Map.empty
ast5 = Seq (Asg "x" (ConstInt 6)) (Whl (Les (Var "x") (ConstInt 5)) (Asg "x" (Mns (Var "x") (ConstInt 1))))
