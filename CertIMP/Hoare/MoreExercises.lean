import CertIMP.Hoare.Logic
import CertIMP.Hoare.Exercises
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open ComEval
open Hoare Proof

/-- Sum of `1 + 2 + … + n`, computed by accumulating into `s`.

    The postcondition is stated multiplied through by `2`, i.e.
    `2 * s = n * (n + 1)`, so that no natural-number division appears.

    Loop invariant: `2 * s = i * (i + 1)`. -/
def sum_first_n {n : ℕ} :
  ⊢ ⦃ ⊤ ⦄
      ⟨{
        s = 0;
        i = 0;
        while i != ↑n do
          i = i + 1;
          s = s + i;
        od
      }⟩
    ⦃ 2 * s = ↑n * (↑n + 1) ⦄ := by
  apply HSeq
  · apply HSeq
    · apply HPostWeaken
      · apply HWhile ⦃ 2 * s = i * (i + 1) ⦄
        apply HSeq
        · apply HAsgn
        apply HPreStrengthen
        · apply HAsgn
        verify_assertion
      verify_assertion
    apply HAsgn
  apply HPreStrengthen
  · apply HAsgn
  verify_assertion
