import CertIMP.StackMachine.Semantics

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

lemma isErrorLemma {err st'} : ¬ Reachable (.error err) st' := by
  intros h
  generalize eq : (Except.error err) = st at h
  induction h with
  | step h => cases eq
  | trans s1 s2 ih1 ih2 =>
    cases eq
    simp only [imp_false, not_true_eq_false] at ih1

lemma isOOFLemma {st} : ¬ Reachable st (.error .OutOfFuel) := by
  intros h
  generalize eq : (Except.error ExecutionException.OutOfFuel) = st' at h
  induction h with
  | @step μ _ h =>
    cases eq
    simp [step, Bind.bind, Except.bind] at h
    aesop
  | trans s1 s2 ih1 ih2 =>
    cases eq
    simp only [imp_false, not_true_eq_false] at ih2

lemma isFinalStepLemma {μ st} (h : isFinal (.ok μ)) :
    step μ = st → isError st := by
  rw [isFinal] at h
  simp only [step, bind, Except.bind, fetchInstr, h, Nat.lt_irrefl, ↓reduceDIte]
  intro h1
  rw [←h1, isError]
  trivial

lemma isFinalLemma {st st'} (h : isFinal st) :
    Reachable st st' → isError st' := by
  intro h
  induction h with
  | @step μ st'' hx =>
    exact isFinalStepLemma h hx
  | @trans _ stx st'' s1 s2 ih1 ih2 =>
    apply ih1 at h
    cases st'' with
    | ok => contradiction
    | error e =>
      have := @isErrorLemma e stx
      contradiction

lemma executeFinal {μ st fuel} (h : isFinal (.ok μ)) :
    execute fuel μ = st → st = .ok μ := by
  intro h1
  rw [execute.eq_def] at h1
  simp [h] at h1
  symm
  assumption

lemma executeExtend {μ μ' fuel} (h : step μ = .ok μ') :
    execute (fuel + 1) μ = execute fuel μ' := by
  rw [execute]
  by_cases hx : μ.pc < μ.code.length
  · rw [h]
    by_cases hf : isFinal (Except.ok μ)
    · rw [isFinal] at hf
      aesop
    · simp [hf]
  · simp [step, hx, Bind.bind, Except.bind] at h

lemma executeStepFinal {μ st} (h1 : isFinal st) (h2 : step μ = st) :
    execute 1 μ = st := by
    rw [execute]
    by_cases hx : μ.pc < μ.code.length
    · have hf : ¬ isFinal (Except.ok μ) := by
        rw [isFinal]
        intro habs
        rw [habs] at hx
        exact Nat.lt_irrefl μ.code.length hx
      rw [h2]
      simp only [hf, ↓reduceIte]
      cases st with
      | ok μ' =>
        simp only [execute, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
        exact h1
      | error => contradiction
    · simp only [step, bind, Except.bind, fetchInstr, hx, ↓reduceDIte] at h2
      rw [←h2] at h1
      contradiction

lemma executeLemmaAux {n : Nat} {μ μ' : MachineState} (h : Reachable (.ok μ) (.ok μ'))
  : ∃m, execute m μ = execute n μ' := by
  generalize eq1 : Except.ok μ = st at h
  generalize eq2 : Except.ok μ' = st' at h
  induction h generalizing n μ μ' with
  | step hs =>
    cases eq1
    cases eq2
    use n + 1
    exact executeExtend hs
  | @trans _ _ sti _ _ ih1 ih2 =>
    cases eq1
    cases eq2
    simp only [Except.ok.injEq, forall_eq_apply_imp_iff] at *
    cases sti with
    | error x =>
      have := @isErrorLemma x (Except.ok μ')
      contradiction
    | ok μi =>
      specialize @ih2 n μi rfl
      obtain ⟨m2, hm2⟩ := ih2
      specialize @ih1 m2 μ μi rfl rfl
      obtain ⟨m1, hm1⟩ := ih1
      rw [hm2] at hm1
      use m1

/-- Hard exercise, you will likely need the lemmas above,
    and possibly additional intermediary results. -/
lemma executeLemma {μ st} (h1 : Reachable (.ok μ) st) (h2 : isFinal st) :
    ∃ fuel : ℕ, execute fuel μ = st := by
  cases st with
  | error => contradiction
  | ok μx =>
    obtain ⟨m, hm⟩ := @executeLemmaAux 0 _ _ h1
    use m
    rw [hm, execute]
    simp [h2]
