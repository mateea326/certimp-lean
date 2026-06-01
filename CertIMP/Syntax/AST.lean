import Mathlib.Data.List.Dedup

abbrev Var : Type := String

/-
  Abstract syntax of arithmetic expressions
-/
inductive AExp where
  | ANum   (n : Nat)
  | AId    (x : Var)
  | APlus  (a1 a2 : AExp)
  | AMinus (a1 a2 : AExp)
  | AMult  (a1 a2 : AExp)
deriving Repr

@[coe, simp]
abbrev var2AExp : Var → AExp := AExp.AId
instance : Coe Var AExp where
  coe := var2AExp
@[coe, simp]
abbrev nat2AExp : Nat → AExp := AExp.ANum
instance : Coe Nat AExp where
  coe := nat2AExp

/-
  Abstract syntax of boolean expressions
-/
inductive BExp where
  | BTrue
  | BFalse
  | BEq    (a1 a2 : AExp)
  | BNeq   (a1 a2 : AExp)
  | BLe    (a1 a2 : AExp)
  | BGt    (a1 a2 : AExp)
  | BNot   (b : BExp)
  | BAnd   (b1 b2 : BExp)
deriving Repr

/-
  Abstract syntax of commands
-/
inductive Com where
  | CSkip
  | CAsgn  (x : Var) (a : AExp)
  | CSeq   (c1 c2 : Com)
  | CIf    (b : BExp) (c1 c2 : Com)
  | CWhile (b : BExp) (c : Com)
deriving Repr

/- List of all variables occurring in an arithmetic expression -/
def AExp.vars : AExp → List Var
  | AId x        => [x]
  | APlus a1 a2  => List.dedup <| a1.vars ++ a2.vars
  | AMinus a1 a2 => List.dedup <| a1.vars ++ a2.vars
  | AMult a1 a2  => List.dedup <| a1.vars ++ a2.vars
  | _            => []

/- List of all variables occurring in a boolean expression -/
def BExp.vars : BExp → List Var
  | BEq  a1 a2   => List.dedup <| a1.vars ++ a2.vars
  | BNeq a1 a2   => List.dedup <| a1.vars ++ a2.vars
  | BLe  a1 a2   => List.dedup <| a1.vars ++ a2.vars
  | BGt a1 a2    => List.dedup <| a1.vars ++ a2.vars
  | BNot b       => b.vars
  | BAnd b1 b2   => List.dedup <| b1.vars ++ b2.vars
  | _            => []

/- List of all variables occurring in a command -/
def Com.vars : Com → List Var
  | CSkip       => []
  | CAsgn x a   => List.dedup <| x :: a.vars
  | CSeq c1 c2  => List.dedup <| c1.vars ++ c2.vars
  | CIf b c1 c2 => List.dedup <| b.vars ++ c1.vars ++ c2.vars
  | CWhile b c  => List.dedup <| b.vars ++ c.vars
