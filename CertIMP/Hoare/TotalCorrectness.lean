import CertIMP.Eval
import CertIMP.Hoare.Exercises

/-
  Partial correctness:
    If `P` is true and `c` terminates, then `Q`.
  
  Total correctness:
    If `P` is true, `c` terminates and `Q`.
    
  Total correctness is `stronger` than partial correctness:
    `total → partial`
-/

namespace Total

open AExp BExp ComEval

def Correct (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ σ, P σ → ∃ σ', σ =[ c ]=> σ' ∧ Q σ'

structure isWeakestPre (c : Com) (Q P : Assertion) where
  isTotalCorrect :  Correct P c Q
  isWeakest      :  ∀ {P'}, Correct P' c Q → P' ->> P

mutual

def wp.P (b : BExp) (c : Com) (Q : Assertion) : ℕ → Assertion
  | 0   => ⦃ ¬↑b ∧ ↑Q ⦄
  | n+1 => ⦃ ↑b ∧ ↑(wp c (wp.P b c Q n)) ⦄

def wp (c : Com) (Q : Assertion) : Assertion := match c with
  | .CSkip       => Q
  | .CAsgn x e   => Q[e // x]
  | .CSeq c₁ c₂  => wp c₁ (wp c₂ Q)
  | .CIf b c₁ c₂ => ⦃ (↑b → ↑(wp c₁ Q)) ∧ (¬↑b → ↑(wp c₂ Q)) ⦄
  | .CWhile b c  => fun σ => ∃ n, wp.P b c Q n σ

end

lemma wpLemma {pgm : Com} :
  wp pgm Q σ ↔ (∃ σ', σ =[pgm]=> σ' ∧ Q σ') := by
  induction pgm generalizing Q σ with
  | CWhile b c ih₁ =>
      unfold wp
      apply Iff.intro
      · intro ⟨n, hn⟩
        induction n generalizing Q σ with
        | zero =>
          simp only [wp.P, Assertion.and, Assertion.neg, assert, Bool.not_eq_true] at hn
          obtain ⟨hn₁, hn₂⟩ := hn
          exists σ
          apply And.intro _ hn₂
          apply EWhileFalse
          assumption
        | succ n ih₂ =>
          simp only [wp.P, Assertion.and, assert] at hn
          obtain ⟨hn₁, hn₂⟩ := hn
          rw [ih₁] at hn₂
          obtain ⟨σ', hn₂, hn₃⟩ := hn₂
          specialize ih₂ hn₃ ; clear hn₃
          obtain ⟨σ'', hn₃, hn₄⟩ := ih₂
          exists σ''
          apply And.intro _ hn₄
          exact .EWhileTrue hn₁ hn₂ hn₃
      · intro ⟨σ', hn₁, hn₂⟩
        generalize heq : Com.CWhile b c = loop at hn₁
        induction hn₁ with
        | EWhileFalse =>
          obtain ⟨_, _⟩ := heq
          exists 0
          simp only [wp.P, Assertion.and, Assertion.neg, assert, Bool.not_eq_true]
          apply And.intro <;>
          assumption
        | EWhileTrue beval ceval weval _ ih =>
          obtain ⟨_, _⟩ := heq
          specialize ih hn₂ rfl
          obtain ⟨n, ih⟩ := ih
          exists n+1
          simp only [wp.P, Assertion.and, assert, beval, true_and]
          rw [ih₁]
          rename_i σ'' _ _
          exists σ''
        | _ => contradiction
  | CSkip =>
      unfold wp
      apply Iff.intro
      · intro h
        exists σ
        apply And.intro .ESkip h
      · intro ⟨_, h1, _⟩
        cases h1
        assumption
  | CAsgn x e =>
      unfold wp
      apply Iff.intro
      · intro h
        unfold Assertion.subst at h
        exists σ[x ↦ AExp.eval σ e]
        apply And.intro _ h
        apply EAsgn rfl rfl
      · intro ⟨_, h, hq⟩
        cases h
        aesop
  | CSeq c₁ c₂ ih₁ ih₂ =>
      unfold wp
      apply Iff.intro
      · intro h
        rw [ih₁] at h
        obtain ⟨σ', h1, h2⟩ := h
        rw [ih₂] at h2
        obtain ⟨σ'', h2, h3⟩ := h2
        exists σ''
        apply And.intro _ h3
        apply ESeq h1 h2
      · intro ⟨σ', h1, h2⟩
        rw [ih₁]
        cases h1
        rename_i σ h1 h2
        exists σ
        apply And.intro h1
        rw [ih₂]
        exists σ'
  | CIf b c₁ c₂ ih₁ ih₂ =>
      unfold wp
      apply Iff.intro
      · simp only [Assertion.and, Assertion.impl, assert, Assertion.neg, Bool.not_eq_true, and_imp]
        intro h₁ h₂
        cases heq : b.eval σ
        · specialize h₂ heq
          rw [ih₂] at h₂
          obtain ⟨σ', h₂, h₃⟩ := h₂
          exists σ'
          apply And.intro _ h₃
          apply EIfFalse heq
          exact h₂
        · specialize h₁ heq
          rw [ih₁] at h₁
          obtain ⟨σ', h₂, h₃⟩ := h₁
          exists σ'
          apply And.intro _ h₃
          apply EIfTrue heq
          exact h₂
      · intro ⟨σ, h₁, h₂⟩
        cases h₁ <;> aesop

lemma wpIsWeakest {pgm : Com} :
  isWeakestPre pgm Q (wp pgm Q) := by
  apply isWeakestPre.mk
  · intro σ
    simp [wpLemma]
  · intro P' h1 σ h2
    obtain ⟨σ', h3, h4⟩ := h1 σ h2
    rw [wpLemma]
    exists σ'

end Total
