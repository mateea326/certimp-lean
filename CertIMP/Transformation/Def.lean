import CertIMP.Equiv

open PgmEquiv

/-- A transformation of arithmetic expressions maps `AExp`s to `AExp`s -/
def ATrans : Type := AExp → AExp

/-- A transformation of boolean expressions maps `AExp`s to `AExp`s -/
def BTrans : Type := BExp → BExp

/-- A `program transformation` is a function that takes a program as input and produces a
    modified program as output.
    Compiler optimizations such as constant folding are canonical examples,
    but there are many others.
-/
def CTrans : Type := Com → Com

/-
  A program transformation is `sound` if it preserves the behavior of the original program.
-/

def ATrans.sound (trans : ATrans) : Prop := ∀ (a : AExp), a ≃ trans a

def BTrans.sound (trans : BTrans) : Prop := ∀ (b : BExp), b ≃ trans b

def CTrans.sound (trans : CTrans) : Prop := ∀ (c : Com), c ≃ trans c
