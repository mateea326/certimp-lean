import CertIMP.Eval.Eval

/-! # Determinism of the big-step semantics

This file proves that the big-step evaluation relation `ComEval` is
*deterministic*: starting from a fixed state `σ`, a command `c` can lead to at
most one final state. This is a fundamental metatheoretic property (Software
Foundations, `Imp`/`ceval_deterministic`) and it is not derived anywhere else in
the development.

The proof is by induction on the first derivation, with the final state of the
second derivation generalised so that the induction hypotheses can be applied to
it. Cases that mix `EIfTrue`/`EIfFalse` (resp. `EWhileFalse`/`EWhileTrue`) are
ruled out because the guard cannot evaluate to both `true` and `false`. -/

open ComEval

/-- Big-step evaluation is deterministic: from a fixed starting state `σ`, the
    command `c` determines its final state uniquely. Stated in a curried form so
    that the induction hypotheses are quantified over the second final state. -/
theorem ceval_deterministic {σ σ₁ : State} {c : Com}
    (h₁ : σ =[c]=> σ₁) : ∀ {σ₂ : State}, σ =[c]=> σ₂ → σ₁ = σ₂ := by
  induction h₁ with
  | ESkip =>
      intro σ₂ h₂
      cases h₂
      rfl
  | EAsgn hn hs =>
      intro σ₂ h₂
      cases h₂
      subst_vars
      rfl
  | ESeq _ _ ih₁ ih₂ =>
      intro σ₂ h₂
      cases h₂ with
      | ESeq hc₁ hc₂ =>
          have e := ih₁ hc₁
          subst e
          exact ih₂ hc₂
  | EIfTrue hb _ ih =>
      intro σ₂ h₂
      cases h₂ with
      | EIfTrue _ hc'  => exact ih hc'
      | EIfFalse hb' _ => rw [hb] at hb'; contradiction
  | EIfFalse hb _ ih =>
      intro σ₂ h₂
      cases h₂ with
      | EIfTrue hb' _  => rw [hb] at hb'; contradiction
      | EIfFalse _ hc' => exact ih hc'
  | EWhileFalse hb =>
      intro σ₂ h₂
      cases h₂ with
      | EWhileFalse _     => rfl
      | EWhileTrue hb' _ _ => rw [hb] at hb'; contradiction
  | EWhileTrue hb _ _ ihc ihloop =>
      intro σ₂ h₂
      cases h₂ with
      | EWhileFalse hb'        => rw [hb] at hb'; contradiction
      | EWhileTrue _ hc' hloop' =>
          have e := ihc hc'
          subst e
          exact ihloop hloop'

/-- Uncurried statement of determinism: two evaluations of the same command from
    the same starting state reach the same final state. -/
theorem ceval_deterministic' {σ σ₁ σ₂ : State} {c : Com}
    (h₁ : σ =[c]=> σ₁) (h₂ : σ =[c]=> σ₂) : σ₁ = σ₂ :=
  ceval_deterministic h₁ h₂
