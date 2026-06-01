import CertIMP.Transformation.Def

/-
  We now look at some example program transformations.

  An expression is *constant* if it contains no variable references.

  `Constant folding` is an optimization that finds constant expressions and replaces them
  by their values.
-/

open AExp BExp

def AExp.fold_constants : ATrans
  | ANum n      => ANum n
  | AId x       => AId x
  | APlus a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => ANum (n₁ + n₂)
      | _, _ =>  APlus a₁.fold_constants a₂.fold_constants
  | AMinus a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => ANum (n₁ - n₂)
      | _, _ =>  AMinus a₁.fold_constants a₂.fold_constants
  | AMult a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => ANum (n₁ * n₂)
      | _, _ =>  AMult a₁.fold_constants a₂.fold_constants

def BExp.fold_constants : BTrans
  | BTrue      => BTrue
  | BFalse     => BFalse
  | BEq a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => if n₁ == n₂ then BTrue else BFalse
      | a₁', a₂'         => BEq a₁' a₂'
  | BNeq a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => if n₁ != n₂ then BTrue else BFalse
      | a₁', a₂'         => BNeq a₁' a₂'
  | BLe a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => if n₁ <= n₂ then BTrue else BFalse
      | a₁', a₂'         => BLe a₁' a₂'
  | BGt a₁ a₂ =>
      match a₁.fold_constants, a₂.fold_constants with
      | ANum n₁, ANum n₂ => if n₁ > n₂ then BTrue else BFalse
      | a₁', a₂'         => BGt a₁' a₂'
  | BNot b    =>
      match b.fold_constants with
      | BTrue  => BFalse
      | BFalse => BTrue
      | b'     => BNot b'
  | BAnd b₁ b₂ =>
      match b₁.fold_constants, b₂.fold_constants with
      | BTrue, BTrue  => BTrue
      | BFalse, BTrue => BFalse
      | BFalse, BFalse => BFalse
      | BTrue, BFalse  => BFalse
      | b₁', b₂'      => BAnd b₁' b₂'

def Com.fold_constants : CTrans
  | CSkip       => ⟨{ skip }⟩
  | CAsgn x a   => ⟨{ ↑x = ↑a.fold_constants }⟩
  | CSeq c₁ c₂  => ⟨{ ↑c₁.fold_constants ; ↑c₂.fold_constants }⟩
  | CIf b c₁ c₂ =>
      match b.fold_constants with
      | BTrue  => c₁
      | BFalse => c₂
      | b'     => ⟨{ if ↑b' then ↑c₁ else ↑c₂ endif }⟩
  | CWhile b c  =>
      match b.fold_constants with
      | BTrue  => ⟨{ while btrue do skip od }⟩
      | BFalse => ⟨{ skip }⟩
      | b'     => ⟨{ while ↑b' do ↑c od }⟩

example : aexp⟨{ (1 + 2) * x }⟩.fold_constants = aexp⟨{ 3 * x }⟩ := rfl
example : aexp⟨{ x - (0 * 6 + y) }⟩.fold_constants = aexp⟨{ x - (0 + y) }⟩ := rfl
example : bexp⟨{ btrue && !(bfalse && btrue) }⟩.fold_constants = bexp⟨{ btrue }⟩ := rfl
example : bexp⟨{ x == y && (0 == (2 - (1 + 1))) }⟩.fold_constants = bexp⟨{ x == y && btrue }⟩ := rfl

example : ⟨{
    x = 4 + 5;
    y = x - 3;
    if (x - y) == (2 + 4) then
      skip;
    else
      y = 0
    endif;
    if 0 <= (4 - (2 + 1)) then
      y = 0;
    else
      skip
    endif;
    while y == 0 do
      x = x + 1;
    od
}⟩.fold_constants = ⟨{
    x = 9;
    y = x - 3;
    if (x - y) == 6 then
      skip;
    else
      y = 0;
    endif;
    y = 0;
    while y == 0 do
      x = x + 1;
    od
}⟩ := rfl
