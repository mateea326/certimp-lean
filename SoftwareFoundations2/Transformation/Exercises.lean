import SoftwareFoundations2.Transformation.ConstantFolding

theorem fold_constants_aexp_sound : AExp.fold_constants.sound := by
  intro aexp σ
  induction aexp with
  | ANum n      => rfl
  | AId x       => rfl
  | _ =>
      simp only [AExp.eval, *, AExp.fold_constants]
      split
      · next eq1 eq2 =>
          rw [eq1, eq2]
          rfl
      · next => rfl

theorem fold_constants_bexp_sound : BExp.fold_constants.sound := by
  intro bexp σ
  induction bexp with
  | BTrue      => rfl
  | BFalse     => rfl
  | BEq a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BNeq a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BLe a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BGt a₁ a₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      have : a₁.eval σ = a₁.fold_constants.eval σ := fold_constants_aexp_sound a₁ σ
      rw [this]; clear this
      have : a₂.eval σ = a₂.fold_constants.eval σ := fold_constants_aexp_sound a₂ σ
      rw [this]; clear this
      split <;> aesop
  | BNot b ih  =>
      simp only [BExp.eval, BExp.fold_constants]
      rw [ih]
      split <;> aesop
  | BAnd b₁ b₂ ih₁ ih₂  =>
      simp only [BExp.eval, BExp.fold_constants]
      rw [ih₁, ih₂]
      split <;> aesop

open ComEval

set_option warn.sorry false in
theorem fold_constants_com_sound : Com.fold_constants.sound := by
  intro c σ₁ σ₂
  induction c generalizing σ₁ σ₂ with
  | CSkip       =>
      apply Iff.intro
      case CSkip.mp =>
        intro h
        unfold Com.fold_constants
        exact h
      case CSkip.mpr =>
        intro h
        unfold Com.fold_constants at h
        exact h
  | CAsgn x a   =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
  | CSeq c₁ c₂ h₁ h₂  =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
  | CIf b c₁ c₂ ih₁ ih₂ =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
  | CWhile b c  =>
      -- FILL IN HERE (optional: PR will pass without it)
      sorry
