import SoftwareFoundations2.Eval.State

/-- Evaluating an arithmetic expression in a given state `σ` produces a number. -/
@[simp]
def AExp.eval (σ : State) : AExp → Nat
  | ANum n       => n
  | AId x        => σ x
  | APlus a1 a2  => a1.eval σ + a2.eval σ
  | AMinus a1 a2 => a1.eval σ - a2.eval σ
  | AMult a1 a2  => a1.eval σ * a2.eval σ

/-- Evaluating a boolean expression in a given state `σ` produces a boolean. -/
@[simp]
def BExp.eval (σ : State) : BExp → Bool
  | BTrue      => true
  | BFalse     => false
  | BEq a1 a2  => a1.eval σ == a2.eval σ
  | BNeq a1 a2 => a1.eval σ != a2.eval σ
  | BLe a1 a2  => a1.eval σ <= a2.eval σ
  | BGt a1 a2  => a1.eval σ > a2.eval σ
  | BNot b     => !b.eval σ
  | BAnd b1 b2 => b1.eval σ && b2.eval σ

/-- Evaluating a command in a given state `σ` produces a new state.

    Note that this function is marked as `partial`.
    This means that for some commands it is provided as input,
    it may run forever and fail to return a final state.

    We use the definition below only for debugging. It's basically a really simple interpreter for
    IMP: pass in a command and an initial state, and it will execute the command and (if it
    terminates) yield the final state. Feel free to play with it!

    To prove properties about IMP commands, we will provide a new definition shortly.
    The new definition will be given as a *relation* between states, commands and states;
    not as a *function*.
-/
partial def Com.eval (σ : State) : Com → State
  | CSkip       => σ
  | CAsgn x a   => σ[x ↦ a.eval σ]
  | CSeq c1 c2  => (c2.eval ∘ c1.eval) σ
  | CIf b c1 c2 => if b.eval σ then c1.eval σ else c2.eval σ
  | CWhile b c  => if b.eval σ then ((CWhile b c).eval ∘ c.eval) σ else σ

/-- Evaluates a command and prints computes the value of each program
    variable in the final state `σ'`.
-/
def Com.getOutput (c : Com) (σ : State) : List (Var × Nat) :=
  let σ' := c.eval σ
  List.foldr (fun x acc => ⟨x, σ' x⟩ :: acc) [] c.vars

-- An example:
/--
  info: [("n", 7), ("sum", 28), ("i", 8)]
-/
#guard_msgs in
#eval ⟨{
  sum = 0;
  i = 0;
  while (i <= n) do
    sum = sum + i;
    i = i + 1;
  od
}⟩.getOutput ["n" ↦ 7]

open Com

/-- Big-step evaluation relation: the type `ComEval σ com σ'` is that of *proofs* that evaluating
    command `com` from starting state `σ` yields final state `σ'`.

    Each constructor stands for a possible way of building this proof. -/
inductive ComEval : State → Com → State → Prop where
  | ESkip :
        ComEval σ CSkip σ
  | EAsgn :
        n = a.eval σ →
        σ' = σ[x ↦ n] →
          ComEval σ (CAsgn x a) σ'
  | ESeq :
        ComEval σ c₁ σ'   →
        ComEval σ' c₂ σ'' →
          ComEval σ (CSeq c₁ c₂) σ''
  | EIfTrue :
        b.eval σ = true →
        ComEval σ c₁ σ' →
          ComEval σ (CIf b c₁ c₂) σ'
  | EIfFalse :
        b.eval σ = false →
        ComEval σ c₂ σ' →
          ComEval σ (CIf b c₁ c₂) σ'
  | EWhileFalse :
        b.eval σ = false →
          ComEval σ (CWhile b c) σ
  | EWhileTrue :
        b.eval σ = true →
        ComEval σ c σ' →
        ComEval σ' (CWhile b c) σ'' →
          ComEval σ (CWhile b c) σ''

notation σ:arg " =[" com "]=> " σ':arg => ComEval σ com σ'
syntax term " =[" com "]=> " term : term
macro_rules
  | `($st1 =[ $com:com ]=> $st2) => `(ComEval $st1 ⟨{ $com:com }⟩ $st2)
