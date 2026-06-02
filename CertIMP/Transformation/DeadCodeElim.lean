import CertIMP.Transformation.Def

/-! # Dead-code elimination

This is a second, independent program transformation (alongside constant
folding). It removes statically dead code:

* `skip` on either side of a sequence (`skip; c ≃ c` and `c; skip ≃ c`);
* self-assignments (`x = x ≃ skip`);

recursing through every sub-command. Its soundness reuses the program
equivalences already proved in `Equiv/Exercises.lean`. -/

open PgmEquiv
open AExp
open ComEval

/-- Self-assignment is equivalent to `skip`, for *any* variable.
    (The library's `identity_assignment` is fixed to the variable `"x"`.) -/
theorem self_assign_skip (x : Var) :
    Com.CAsgn x (AExp.AId x) ≃ Com.CSkip := by
  intro σ σ'
  apply Iff.intro
  · intro h
    cases h
    case EAsgn n eqn eqs =>
      subst eqn
      simp only [AExp.eval, State.set_id] at eqs
      subst eqs
      exact ESkip
  · intro h
    cases h
    apply EAsgn rfl
    simp only [AExp.eval, State.set_id]

/-- Smart sequencing that drops a `skip` on either side. -/
def Com.dceSeq : Com → Com → Com
  | CSkip, c₂ => c₂
  | c₁, CSkip => c₁
  | c₁, c₂    => CSeq c₁ c₂

/-- Dead-code elimination. -/
def Com.eliminate_dead_code : CTrans
  | CSkip       => CSkip
  | CAsgn x a   =>
      match a with
      | AId y => if y = x then CSkip else CAsgn x (AId y)
      | _     => CAsgn x a
  | CSeq c₁ c₂  => Com.dceSeq c₁.eliminate_dead_code c₂.eliminate_dead_code
  | CIf b c₁ c₂ => CIf b c₁.eliminate_dead_code c₂.eliminate_dead_code
  | CWhile b c  => CWhile b c.eliminate_dead_code

/-- `dceSeq` preserves behaviour. -/
theorem dceSeq_sound (c₁ c₂ : Com) :
    ⟨{ ↑c₁; ↑c₂ }⟩ ≃ Com.dceSeq c₁ c₂ := by
  cases c₁ <;> cases c₂ <;>
    simp only [Com.dceSeq] <;>
    first
      | exact skip_left
      | exact skip_right
      | exact equiv_refl

/-- **Dead-code elimination is sound**: every command is semantically
    equivalent to its dead-code-eliminated version. -/
theorem eliminate_dead_code_sound : Com.eliminate_dead_code.sound := by
  intro c
  induction c with
  | CSkip =>
      unfold Com.eliminate_dead_code
      exact equiv_refl
  | CAsgn x a =>
      unfold Com.eliminate_dead_code
      cases a with
      | AId y =>
          dsimp only
          split
          · next h => subst h; exact self_assign_skip _
          · exact equiv_refl
      | ANum n      => exact equiv_refl
      | APlus a₁ a₂  => exact equiv_refl
      | AMinus a₁ a₂ => exact equiv_refl
      | AMult a₁ a₂  => exact equiv_refl
  | CSeq c₁ c₂ ih₁ ih₂ =>
      unfold Com.eliminate_dead_code
      have h : ⟨{ ↑c₁; ↑c₂ }⟩ ≃ ⟨{ ↑c₁.eliminate_dead_code; ↑c₂.eliminate_dead_code }⟩ :=
        equiv_trans (equiv_congr_seqL ih₁) (equiv_congr_seqR ih₂)
      exact equiv_trans h (dceSeq_sound _ _)
  | CIf b c₁ c₂ ih₁ ih₂ =>
      unfold Com.eliminate_dead_code
      exact equiv_congr_if ih₁ ih₂
  | CWhile b c ih =>
      unfold Com.eliminate_dead_code
      exact equiv_congr_while ih
