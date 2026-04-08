import SoftwareFoundations2.Eval
import SoftwareFoundations2.Hoare.Exercises

namespace Hoare

open AExp BExp ComEval Proof

structure isWeakestPre (c : Com) (Q P : Assertion) where
  isPartialCorrect : ⊨ ⦃ P ⦄ c ⦃ Q ⦄
  isWeakest        : ∀ {P'}, ⊨ ⦃ P' ⦄ c ⦃ Q ⦄ → P' ->> P

/-- Since we use Lean's `Prop` as an assertion language, it is trivial to define
    a `wlp` assertion that satisfies the `isWeakestPre` requirements: -/
def wlp (c : Com) (Q : Assertion) : Assertion := 
  fun σ => ∀ σ', σ =[c]=> σ' → Q σ'

lemma weakestPreSkip {w : Assertion} (h : isWeakestPre .CSkip Q w) :
    w ->> Q := by
  obtain ⟨parCorr, isWkst⟩ := h
  intro σ h2
  exact parCorr σ σ .ESkip h2

lemma weakestPreAsgn {w : Assertion} (h : isWeakestPre (.CAsgn x e) Q w) :
    w ->> Q[e // x] := by
  obtain ⟨parCorr, isWkst⟩ := h
  intro σ h2
  exact parCorr σ (σ[x ↦ AExp.eval σ e]) (.EAsgn rfl rfl) h2

theorem wlpIsWp {c : Com} {Q : Assertion} : isWeakestPre c Q (wlp c Q) := by
  apply isWeakestPre.mk
  · intro σ σ' h1 h2
    simp only [wlp] at h2
    apply h2
    assumption
  · intro P' h1 σ h2
    simp only [wlp]
    intros
    apply h1
    repeat assumption

def Completeness :
  ⊨ ⦃ P ⦄ c ⦃ Q ⦄ → ⊢ ⦃ P ⦄ c ⦃ Q ⦄ := by
  intro h
  have preWp : isWeakestPre c Q (wlp c Q) := wlpIsWp
  obtain ⟨isPre, isWeakest⟩ := preWp
  specialize isWeakest h
  apply HPreStrengthen _ isWeakest
  clear isWeakest isPre
  cases c with
  | CSkip =>
      apply @HPreStrengthen Q
      · exact HSkip
      · apply weakestPreSkip
        exact wlpIsWp
  | CAsgn x e =>
      apply HPreStrengthen
      · exact HAsgn
      · apply weakestPreAsgn
        exact wlpIsWp
  | CSeq c₁ c₂ =>
      -- Hand-crafting the induction hypotheses:
      obtain ⟨c₂Pre, _⟩ := @wlpIsWp c₂ Q
      obtain c₂Pre := Completeness c₂Pre
      obtain ⟨c₁Pre, _⟩ := @wlpIsWp c₁ (wlp c₂ Q)
      obtain c₁Pre := Completeness c₁Pre
      --
      apply HSeq 
      · exact c₂Pre
      · apply HPreStrengthen c₁Pre
        · simp only [Assertion.implies]
          intro _ h _ h3 st3 h4
          specialize h st3 (.ESeq h3 h4)
          exact h
  | CIf b c₁ c₂ =>
      -- Hand-crafting the induction hypotheses:
      obtain ⟨c₁Pre, _⟩ := @wlpIsWp c₁ Q
      obtain c₁Pre := Completeness c₁Pre
      obtain ⟨c₂Pre, _⟩ := @wlpIsWp c₂ Q
      obtain c₂Pre := Completeness c₂Pre
      --
      apply HIf
      · apply HPreStrengthen c₁Pre
        · simp only [Assertion.implies, Assertion.true, Assertion.impl, Assertion.and, wlp, assert,
          and_imp]
          intro st h h2 st2 h3
          specialize h st2 (.EIfTrue h2 h3)
          exact h
      · apply HPreStrengthen c₂Pre
        · simp only [Assertion.implies, Assertion.true, Assertion.impl, Assertion.and, wlp,
          Assertion.neg, assert, Bool.not_eq_true, and_imp]
          intro st h h2 st2 h3
          specialize h st2 (.EIfFalse h2 h3)
          exact h
  | CWhile b c₀ =>
      apply HPostWeaken
      · apply HWhile (wlp (.CWhile b c₀) Q)
        -- Hand-crafting the induction hypothesis:
        obtain ⟨c₀Pre, _⟩ := @wlpIsWp c₀ (wlp (.CWhile b c₀) Q)
        obtain c₀Pre := Completeness c₀Pre
        --
        apply HPreStrengthen c₀Pre
        simp only [Assertion.implies, Assertion.true, Assertion.impl, Assertion.and, wlp, assert,
          and_imp]
        intro σ h1 hb σ' hc₀ σ'' hwh
        apply h1
        apply EWhileTrue hb hc₀ hwh
      · simp only [Assertion.implies, Assertion.true, Assertion.impl, Assertion.and, Assertion.neg,
        assert, Bool.not_eq_true, and_imp]
        intro σ h1 h2
        apply h1
        apply EWhileFalse h2

end Hoare
