import CertIMP.Hoare.Exercises

open Com Hoare Proof

/-
  Decorated commands: commands decorated with invariants
-/
inductive DCom where
  | DSkip
  | DAsgn  (x : Var) (a : AExp)
  | DSeq   (c1 c2 : DCom)
  | DIf    (b : BExp) (c1 c2 : DCom)
  | DWhile (inv : Assertion) (b : BExp) (c : DCom)

@[coe]
abbrev DCom.undecorate : DCom → Com
  | DSkip        => CSkip
  | DAsgn x a    => CAsgn x a
  | DSeq  c1 c2  => CSeq c1.undecorate c2.undecorate
  | DIf b c1 c2  => CIf b c1.undecorate c2.undecorate
  | DWhile _ b c => CWhile b c.undecorate

abbrev DProof (P : Assertion) (dec : DCom) (Q : Assertion) := Hoare.Proof P dec.undecorate Q
