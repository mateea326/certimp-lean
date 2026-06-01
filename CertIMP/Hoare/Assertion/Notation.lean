import CertIMP.Hoare.Assertion.Assertion

import Lean

open Lean

notation "ATrue" => Assertion.top
notation "AFalse" => Assertion.bot
prefix:100 "¬" => Assertion.neg
infix:99 " ∧ " => Assertion.and
infix:99 " ∨  " => Assertion.or
infix:80 " → " => Assertion.impl

declare_syntax_cat assertTerm
declare_syntax_cat assert

syntax num   : assertTerm
syntax ident : assertTerm
syntax str : assertTerm -- todo...
syntax:max "↑" term:arg : assertTerm -- todo...
syntax:50 assertTerm:49 " * " assertTerm:48 : assertTerm
syntax:50 assertTerm:49 " / " assertTerm:48 : assertTerm
syntax:45 assertTerm:44 " % " assertTerm:43 : assertTerm
syntax:40 assertTerm:39 " + " assertTerm:38 : assertTerm
syntax:40 assertTerm:39 " - " assertTerm:38 : assertTerm
syntax:max "(" assertTerm ")" : assertTerm -- todo...

syntax "T" : assert
syntax "⊤" : assert
syntax "F" : assert
syntax "⊥" : assert
--syntax ident : assert
syntax:100 assertTerm " = " assertTerm : assert
syntax:100 assertTerm " != " assertTerm : assert
syntax:100 assertTerm " ≠ " assertTerm : assert
syntax:100 assertTerm " <= " assertTerm : assert
syntax:100 assertTerm " ≤ " assertTerm : assert
syntax:100 assertTerm " < " assertTerm : assert
syntax:100 assertTerm " >= " assertTerm : assert
syntax:100 assertTerm " ≥ " assertTerm : assert
syntax:100 assertTerm " > " assertTerm : assert
syntax:101 "¬" assert:100 : assert
syntax:99 assert:97 " ∧ " assert:98 : assert
syntax:99 assert:97 " ∨ " assert:98 : assert
syntax:80 assert:78 " → " assert:79 : assert
syntax:80 assert:78 " ↔ " assert:90 : assert
syntax:max "(" assert ")" : assert
syntax:max "↑" term:arg   : assert

syntax "T⦃" assertTerm "⦄" : term
syntax "⦃" assert "⦄" : term

macro_rules
  | `(T⦃ $n:num ⦄ )   => `(Eval.eval $n)
  | `(T⦃ $s:str ⦄ )   => `(Eval.eval $s) -- todo...
  | `(T⦃ ↑$t ⦄ )      => `(Eval.eval $t) -- todo...
  | `(T⦃ ($t:assertTerm) ⦄ )  => `(T⦃ $t:assertTerm ⦄ )
  | `(T⦃ $x + $y ⦄ )  => `(Eval.add T⦃ $x ⦄ T⦃ $y ⦄)
  | `(T⦃ $x - $y ⦄ )  => `(Eval.sub T⦃ $x ⦄ T⦃ $y ⦄)
  | `(T⦃ $x * $y ⦄ )  => `(Eval.mul T⦃ $x ⦄ T⦃ $y ⦄)
  | `(T⦃ $x / $y ⦄ )  => `(Eval.div T⦃ $x ⦄ T⦃ $y ⦄)
  | `(T⦃ $x % $y ⦄ )  => `(Eval.mod T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ T ⦄ )         => `(Assertion.top)
  | `(⦃ ⊤ ⦄ )         => `(Assertion.top)
  | `(⦃ F ⦄ )         => `(Assertion.bot)
  | `(⦃ ⊥ ⦄ )         => `(Assertion.bot)
  | `(⦃ $x:assertTerm = $y:assertTerm ⦄ )  => `(Assertion.eq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm != $y:assertTerm ⦄ )  => `(Assertion.neq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm ≠ $y:assertTerm ⦄ )  => `(Assertion.neq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm <= $y:assertTerm ⦄ ) => `(Assertion.leq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm ≤ $y:assertTerm ⦄ )  => `(Assertion.leq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm < $y:assertTerm ⦄ )  => `(Assertion.le T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm >= $y:assertTerm ⦄ ) => `(Assertion.geq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm ≥ $y:assertTerm ⦄ )  => `(Assertion.geq T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $x:assertTerm > $y:assertTerm ⦄ )  => `(Assertion.ge T⦃ $x ⦄ T⦃ $y ⦄)
  | `(⦃ $a₁ → $a₂ ⦄ ) => `(Assertion.impl ⦃ $a₁ ⦄ ⦃ $a₂ ⦄)
  | `(⦃ $a₁ ↔ $a₂ ⦄ ) => `(Assertion.iff ⦃ $a₁ ⦄ ⦃ $a₂ ⦄)
  | `(⦃ $a₁ ∨ $a₂ ⦄ ) => `(Assertion.or ⦃ $a₁ ⦄ ⦃ $a₂ ⦄)
  | `(⦃ $a₁ ∧ $a₂ ⦄ ) => `(Assertion.and ⦃ $a₁ ⦄ ⦃ $a₂ ⦄)
  | `(⦃ ¬$a ⦄ )       => `(Assertion.neg ⦃ $a ⦄)
  | `(⦃ ($a) ⦄ )      => `( ⦃ $a ⦄ ) 

open Elab Term Meta PrettyPrinter

elab_rules : term
  | `(T⦃ $id:ident ⦄ ) => do
    let isProperIdent ← Elab.Term.isLocalIdent? id
    match isProperIdent with
    | some _ =>
        let e ← elabTerm id none
        let ty ← inferType e
        -- If expression has type `ValThunk` already, no need to synthesize
        -- `Eval` class instance:
        if (← isDefEq (← inferType e) (mkConst ``ValThunk [])) then
          return e
        -- Else, attempt to synthesize...
        let mvar ← mkFreshExprMVar
            (type? := some <| mkAppN (mkConst ``Eval []) #[ty]) (kind := .synthetic)
        let succ ← synthesizeInstMVarCore mvar.mvarId!
        let inst ← instantiateMVars mvar
        unless succ do
          throwError s!"failed to synthesize Eval instance for {ty}"
        return mkAppN (.const ``Eval.eval []) #[ty, inst, e]
    | none =>
        let e := mkStrLit id.getId.toString
        return mkAppN (.const ``Eval.eval []) #[.const ``Var [], .const ``instEvalVar [], e]
  --| `(⦃ $id:ident ⦄ ) => do
  --    let e ← elabTerm id (some (.const `Assertion []))
  --    return e
  | `(⦃ ↑$t:term ⦄ ) => do
      let e ← elabTerm t (some (.const `Assertion []))
      return e

@[app_unexpander Eval.eval]
def unexpandEval : Unexpander
  | `($_ $arg) => `(term| $arg)
  | _ => throw ()

@[app_unexpander Eval.add]
def unexpandAdd : Unexpander
  | `($_ $l $r) => `(term| $l + $r)
  | _ => throw ()

@[app_unexpander Eval.sub]
def unexpandSub : Unexpander
  | `($_ $l $r) => `(term| $l - $r)
  | _ => throw ()

@[app_unexpander Eval.mul]
def unexpandMul : Unexpander
  | `($_ $l $r) => `(term| $l * $r)
  | _ => throw ()

@[app_unexpander Eval.div]
def unexpandDiv : Unexpander
  | `($_ $l $r) => `(term| $l / $r)
  | _ => throw ()

@[app_unexpander Eval.mod]
def unexpandMod : Unexpander
  | `($_ $l $r) => `(term| $l % $r)
  | _ => throw ()

@[app_unexpander Assertion.top]
def unexpandTop : Unexpander
  | `($_) => `(assert| ⊤)

@[app_unexpander Assertion.bot]
def unexpandBot : Unexpander
  | `($_) => `(assert| ⊥)
 
@[app_unexpander Assertion.eq]
def unexpandEq : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm = $(⟨rhs.raw⟩))
  | _ => throw ()

@[app_unexpander Assertion.leq]
def unexpandLeq : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm ≤ $(⟨rhs.raw⟩))
  | _ => throw ()

@[app_unexpander Assertion.le]
def unexpandLe : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm < $(⟨rhs.raw⟩))
  | _ => throw ()


@[app_unexpander Assertion.ge]
def unexpandGe : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm > $(⟨rhs.raw⟩))
  | _ => throw ()

@[app_unexpander Assertion.geq]
def unexpandGeq : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm ≥ $(⟨rhs.raw⟩))
  | _ => throw ()

@[app_unexpander Assertion.neq]
def unexpandNeq : Unexpander
  | `($_ $lhs $rhs) => `(assert| $(⟨lhs.raw⟩):assertTerm ≠ $(⟨rhs.raw⟩))
  | _ => throw ()

@[app_unexpander BExp.assert]
def unexpandBAssert : Unexpander
  | `($_ $b) => `(term| $b)
  | _ => throw ()

attribute [aesop norm unfold (rule_sets := [assertion])] BExp.assert
attribute [aesop norm unfold (rule_sets := [assertion])] ValThunk.ofNat
attribute [aesop norm unfold (rule_sets := [assertion])] ValThunk.ofVar
attribute [aesop norm unfold (rule_sets := [assertion])] ValThunk.ofAExp
attribute [aesop norm unfold (rule_sets := [assertion])] Eval.add
attribute [aesop norm unfold (rule_sets := [assertion])] Eval.sub
attribute [aesop norm unfold (rule_sets := [assertion])] Eval.mul
attribute [aesop norm unfold (rule_sets := [assertion])] toAssert
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.implies
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.top
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.bot
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.eq
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.neq
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.leq
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.le
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.geq
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.ge
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.impl
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.iff
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.or
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.and
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.neg
attribute [aesop norm unfold (rule_sets := [assertion])] Assertion.subst
attribute [aesop norm unfold (rule_sets := [assertion])] State.set
attribute [aesop norm (rule_sets := [assertion])] State.set_id
attribute [aesop norm (rule_sets := [assertion])] State.set_comm

macro "verify_assertion" : tactic =>
  `(tactic| simp_all [BExp.assert, ValThunk.ofNat, ValThunk.ofVar, ValThunk.ofAExp,
            Eval.add, Eval.sub, Eval.mul, toAssert, Assertion.true, Assertion.implies,
            Assertion.top, Assertion.bot, Assertion.eq, Assertion.neq,
            Assertion.leq, Assertion.le, Assertion.geq, Assertion.ge,
            Assertion.impl, Assertion.iff, Assertion.or, Assertion.and,
            Assertion.neg, Assertion.subst, State.set, State.set_id,
State.set_comm] <;> first | grind | aesop (config := { warnOnNonterminal := false }) <;> try omega)
