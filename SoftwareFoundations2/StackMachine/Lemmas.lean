import SoftwareFoundations2.StackMachine.Semantics

/-
  All exercises in this file are optional, but they may be a very good exercise to get a grasp
  of the transition system we are compiling IMP to.
-/

-- When you use `simp` in this file,
-- all of the following definitions will automatically be unfolded:
attribute [local simp] step
attribute [local simp] replaceMemStackAndIncrPC
attribute [local simp] replaceStackAndIncrPC
attribute [local simp] incrPC
attribute [local simp] fetchInstr
attribute [local simp] stackPeek2
attribute [local simp] stackPeek1

set_option warn.sorry false in
lemma isErrorLemma {err st'} : ¬ Reachable (.error err) st' := by
  sorry

set_option warn.sorry false in
lemma isOOFLemma {st} : ¬ Reachable st (.error .OutOfFuel) := by
  sorry

set_option warn.sorry false in
lemma isFinalStepLemma {μ st} (h : isFinal (.ok μ)) :
    step μ = st → isError st := by
  sorry

set_option warn.sorry false in
lemma isFinalLemma {st st'} (h : isFinal st) :
    Reachable st st' → isError st' := by
  sorry

set_option warn.sorry false in
lemma executeFinal {μ st fuel} (h : isFinal (.ok μ)) :
    execute fuel μ = st → st = .ok μ := by
  sorry

set_option warn.sorry false in
lemma executeExtend {μ μ' fuel} (h : step μ = .ok μ') :
    execute (fuel + 1) μ = execute fuel μ' := by
  sorry

set_option warn.sorry false in
lemma executeStepFinal {μ st} (h1 : isFinal st) (h2 : step μ = st) :
    execute 1 μ = st := by
  sorry

set_option warn.sorry false in
/-- Hard exercise, you will likely need the lemmas above,
    and possibly additional intermediary results. -/
lemma executeLemma {μ st} (h1 : Reachable (.ok μ) st) (h2 : isFinal st) :
    ∃ fuel : ℕ, execute fuel μ = st := by
  sorry
