import CertIMP.Eval

def Assertion := State → Prop

variable {x y z : Var}

example : Assertion :=
  fun σ => σ x ≤ σ y
example : Assertion :=
  fun σ => σ x = 3 ∨ σ x ≤ σ y
example : Assertion :=
  fun σ => σ z * σ z ≤ σ x ∧ ¬((σ z + 1) * (σ z + 1) ≤ σ x)
example : Assertion :=
  fun σ => σ z = max (σ x) (σ y)

@[simp]
abbrev BExp.assert (b : BExp) : Assertion := fun σ => b.eval σ = true
instance : Coe BExp Assertion where
  coe := BExp.assert

def Assertion.subst (P : Assertion) (x : Var) (a : AExp) : Assertion :=
  fun σ => P (σ[x ↦ a.eval σ])

notation P "[" a " // " x "]" => Assertion.subst P x a

@[simp] abbrev Assertion.true (P : Assertion) : Prop := ∀ σ, P σ

abbrev ValThunk := State → ℕ

class Eval (α : Type) where
  eval : α → ValThunk

@[simp] abbrev ValThunk.ofNat (n : ℕ) : ValThunk := fun _ => n
@[simp] abbrev ValThunk.ofVar (x : Var) : ValThunk := fun σ => σ x
@[simp] abbrev ValThunk.ofAExp (a : AExp) : ValThunk := fun σ => a.eval σ
@[simp] instance instEvalNat : Eval ℕ where
  eval := ValThunk.ofNat
@[simp] instance instEvalVar : Eval Var where
  eval := ValThunk.ofVar
@[simp] instance instEvalString : Eval String where
  eval := ValThunk.ofVar
@[simp] instance instEvalAExp : Eval AExp where
  eval := ValThunk.ofAExp

@[simp]
abbrev Eval.add (x y : ValThunk) : ValThunk := fun σ => x σ + y σ 
@[simp]
abbrev Eval.sub (x y : ValThunk) : ValThunk := fun σ => x σ - y σ 
@[simp]
abbrev Eval.mul (x y : ValThunk) : ValThunk := fun σ => x σ * y σ 
@[simp]
abbrev Eval.div (x y : ValThunk) : ValThunk := fun σ => x σ / y σ
@[simp]
abbrev Eval.mod (x y : ValThunk) : ValThunk := fun σ => x σ % y σ 

@[simp] abbrev toAssert : (State → Prop) → Assertion   := id

@[simp] abbrev Assertion.top : Assertion :=
  fun _ => True
@[simp] abbrev Assertion.bot : Assertion :=
  fun _ => False
@[simp] abbrev Assertion.eq (x y : ValThunk) : Assertion :=
  fun σ => x σ = y σ
@[simp] abbrev Assertion.neq (x y : ValThunk) : Assertion :=
  fun σ => x σ ≠ y σ
@[simp] abbrev Assertion.leq (x y : ValThunk) : Assertion :=
  fun σ => x σ ≤ y σ
@[simp] abbrev Assertion.le (x y : ValThunk) : Assertion :=
  fun σ => x σ < y σ
@[simp] abbrev Assertion.geq (x y : ValThunk) : Assertion :=
  fun σ => x σ ≥ y σ
@[simp] abbrev Assertion.ge (x y : ValThunk) : Assertion :=
  fun σ => x σ > y σ
@[simp] abbrev Assertion.impl (P : Assertion) (Q : Assertion) : Assertion :=
  fun σ => P σ → Q σ
@[simp] abbrev Assertion.iff (P : Assertion) (Q : Assertion) : Assertion :=
  fun σ => P σ ↔ Q σ
@[simp] abbrev Assertion.or (P : Assertion) (Q : Assertion) : Assertion :=
  fun σ => P σ ∨ Q σ
@[simp] abbrev Assertion.and (P : Assertion) (Q : Assertion) : Assertion :=
  fun σ => P σ ∧ Q σ
@[simp] abbrev Assertion.neg (P : Assertion) : Assertion :=
  fun σ => ¬P σ

declare_aesop_rule_sets [assertion] (default := false)

@[simp] abbrev Assertion.implies (P Q : Assertion) : Prop :=
  (P.impl Q).true

@[simp] def Assertion.bothElimL {P Q : Assertion} (h : (P.and Q).true) : P.true :=
  fun σ => (h σ).1
@[simp] def Assertion.bothElimR {P Q : Assertion} (h : (P.and Q).true) : Q.true :=
  fun σ => (h σ).2

infixr:80 " ->> " => Assertion.implies
