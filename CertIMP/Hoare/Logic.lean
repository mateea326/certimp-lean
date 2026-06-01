import CertIMP.Hoare.Assertion

namespace Hoare

def Valid (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ σ σ', σ =[ c ]=> σ' → P σ → Q σ'

inductive Proof : Assertion → Com → Assertion → Type where
  | HSkip {P} :
        Proof P ⟨{ skip }⟩ P
  | HAsgn :
        Proof (P[a // x]) ⟨{ ↑x = ↑a }⟩ P
  | HSeq :
      Proof Q d R →
      Proof P c Q →
        Proof P ⟨{ ↑c; ↑d }⟩ R
  | HIf {b : BExp} :
      Proof (P ∧ b) c₁ Q → 
      Proof (P ∧ ¬b) c₂ Q →
        Proof P ⟨{ if ↑b then ↑c₁ else ↑c₂ endif }⟩ Q
  | HWhile {b : BExp} (P) :
      Proof (P ∧ b) c P →
        Proof P ⟨{ while ↑b do ↑c od }⟩ (P ∧ ¬b )
  | HConsequence:
      Proof P' c Q' → 
      (Q' ->> Q) →
      (P ->> P') →
        Proof P c Q

notation "⊨ " "⦃ " P " ⦄ " c:arg " ⦃ " Q " ⦄" => Valid P c Q
macro "⊨ " "⦃ " P:assert " ⦄ " c:term:arg " ⦃ " Q:assert " ⦄" : term =>
  `(Valid ⦃ $P ⦄ $c ⦃ $Q ⦄ )

notation "⊢ " "⦃ " P " ⦄ " c:arg " ⦃ " Q " ⦄" => Proof P c Q
macro "⊢ " "⦃ " P:assert " ⦄ " c:term:arg " ⦃ " Q:assert " ⦄" : term =>
  `(Proof ⦃ $P ⦄ $c ⦃ $Q ⦄)

end Hoare
