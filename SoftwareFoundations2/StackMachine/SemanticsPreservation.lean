import SoftwareFoundations2.StackMachine.Compile
import SoftwareFoundations2.StackMachine.Lemmas
import SoftwareFoundations2.Eval.Eval

set_option linter.style.longLine false
attribute [local simp] Except.instMonad
attribute [local simp] Except.bind

open Instruction AExp BExp

@[simp]
def Bool.toValue : Bool → Value
  | false => 0
  | true  => 1

/- The bulk of work for semantics preservation will be handled by the following
   auxiliary lemmas: -/

lemma AExp.compileCorrectAux {pre suf stack mem} (a : AExp) :
  Reachable
    (.ok ⟨pre ++ (a.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (a.compile ++ suf), a.eval mem :: stack, mem, (pre ++ a.compile).length⟩) := by
    sorry

lemma BExp.compileCorrectAux {pre suf stack mem} (b : BExp) :
  Reachable
    (.ok ⟨pre ++ (b.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (b.compile ++ suf), (b.eval mem).toValue :: stack, mem, (pre ++ b.compile).length⟩) := by
    sorry

/- For this proof, don't be set off if it becomes super technical and long.
   You can likely split the definition of Com.compileOffset into multiple sub-operations,
   and prove sub-lemmas for each sub-operation.
   But you don't have to; the naive way of proving this will likely suffice.
-/
lemma Com.compileCorrectAux (pgm σ σ' stack pre suf) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ, pre.length⟩)
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ', (pre ++ pgm.compileOffset pre.length).length⟩) := by
    sorry

lemma Com.compileCorrectAux2 (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pgm.compile, stack, σ, 0⟩)
    (.ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩) := by
    sorry

/- With these lemmas on hand, proving correctness of compilation for {`AExp`, `BExp`, whole programs} is an easy consequence.
  I kept the proofs in full, they do not need to be filled out.
  Try to work out their reasoning and understand how the lemmas come into play!
  
  Important: `executeLemma` plays a crucial role here, which is marked as a
  hard optional exercise in `Lemmas.lean`. Why is it so important?
-/

theorem AExp.compileCorrect (a : AExp) (σ stack) :
  ∃ fuel : ℕ,
    execute fuel ⟨a.compile, stack, σ, 0⟩ =
      .ok ⟨a.compile, a.eval σ :: stack, σ, a.compile.length⟩ := by
  apply executeLemma
  · have := AExp.compileCorrectAux (pre := []) (suf := []) (mem := σ) (stack := stack) a
    simp only [List.append_nil, List.nil_append, List.length_nil] at this
    apply this
  · simp only [isFinal]

theorem BExp.compileCorrect (b : BExp) (σ stack) :
  ∃ fuel : ℕ,
    execute fuel ⟨b.compile, stack, σ, 0⟩ =
      .ok ⟨b.compile, (b.eval σ).toValue :: stack, σ, b.compile.length⟩ := by
  apply executeLemma
  · have := BExp.compileCorrectAux (pre := []) (suf := []) (mem := σ) (stack := stack) b
    simp only [List.append_nil, List.nil_append, List.length_nil] at this
    apply this
  · simp only [isFinal]

theorem Com.compileCorrect (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  ∃ fuel : ℕ,
    execute fuel ⟨pgm.compile, stack, σ, 0⟩ = .ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩ := by
  apply executeLemma
  · apply compileCorrectAux2
    assumption
  · simp only [isFinal]
