import CertIMP.Hoare.Logic

open AExp
open BExp

namespace Hoare

lemma hoare_skip : ⊨ ⦃ P ⦄ ⟨{ skip }⟩ ⦃ P ⦄ := by
  intros σ σ' h p
  cases h
  assumption

lemma hoare_asgn : ⊨ ⦃ P[a // x] ⦄ ⟨{ ↑x = ↑a }⟩ ⦃ P ⦄ := by
  intros σ σ' h p
  cases h
  case EAsgn n na σ'σ =>
    rw [σ'σ, na]
    rw [Assertion.subst] at p
    assumption

lemma hoare_seq
    (h₁ : ⊨ ⦃ P ⦄ c₁ ⦃ Q ⦄)
    (h₂ : ⊨ ⦃ Q ⦄ c₂ ⦃ R ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ ↑c₁ ; ↑c₂}⟩ ⦃ R ⦄ := by
  intros σ σ' h p
  cases h
  case ESeq σ'' σσ'' σ''σ' =>
    specialize h₁ σ σ'' σσ'' p
    exact h₂ σ'' σ' σ''σ' h₁

lemma hoare_if {b : BExp}
      (h₁ : ⊨ ⦃ P ∧ b ⦄ c₁ ⦃ Q ⦄)
      (h₂ : ⊨ ⦃ P ∧ ¬b ⦄ c₂ ⦃ Q ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ ⦃ Q ⦄ := by
  intros σ σ' h p
  cases h
  case EIfTrue bt c₁' =>
    specialize h₁ σ σ' c₁'
    apply h₁
    unfold Assertion.and
    exact And.intro p bt
  case EIfFalse bf c₂' =>
    specialize h₂ σ σ' c₂'
    apply h₂
    unfold Assertion.and
    unfold Assertion.neg
    simp only [Bool.not_eq_true]
    exact And.intro p bf

lemma hoare_while {b : BExp}
      (h : ⊨ ⦃ P ∧ b ⦄ c ⦃ P ⦄) :
  ⊨ ⦃ P ⦄ ⟨{ while ↑b do ↑c od }⟩ ⦃ P ∧ ¬b ⦄ := by
  generalize W : ⟨{ while ↑b do ↑c od }⟩ = loop
  intros σ σ' h' p
  induction h' with
  | EWhileFalse bf =>
    simp only [Com.CWhile.injEq] at W
    unfold Assertion.and
    unfold Assertion.neg
    simp only [Bool.not_eq_true]
    rcases W with ⟨bb', _⟩
    rw [bb']
    exact And.intro p bf
  | @EWhileTrue σ'' c' σ''' b' σ'''' bt σ''σ''' σ'''σ'''' h' h'' =>
    specialize h'' W
    apply h''
    simp only [Com.CWhile.injEq] at W
    rcases W with ⟨bb_cross, cc_cross⟩
    rw [bb_cross, cc_cross] at h
    specialize h σ'' σ''' σ''σ'''
    unfold Assertion.and at h
    exact h (And.intro p bt)
  | _ => aesop

lemma hoare_consequence
    (hPre : P ->> P')
    (hPost : Q' ->> Q)
    (hH : ⊨ ⦃ P' ⦄ c ⦃ Q' ⦄) :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intros σ σ' h p
  unfold Assertion.implies at hPre
  unfold Assertion.implies at hPost
  specialize hPre σ p
  specialize hPost σ'
  specialize hH σ σ' h hPre
  exact hPost hH

def Soundness :
  ⊢ ⦃ P ⦄ c ⦃ Q ⦄ → ⊨ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intro h
  induction h with
  | HSkip =>
      exact hoare_skip
  | HAsgn =>
      exact hoare_asgn
  | @HSeq P c₁ Q c₂ R _ _ ih₁ ih₂ =>
      apply hoare_seq
      repeat assumption
  | HIf _ _ ih₁ ih₂ =>
      apply hoare_if ih₁ ih₂
  | @HWhile P c b _ ih =>
      apply hoare_while ih
  | HConsequence h₁ h₂ _ ih =>
      apply hoare_consequence
      repeat assumption

end Hoare
