import CertIMP.StackMachine.Compile
import CertIMP.StackMachine.Lemmas
import CertIMP.Eval.Eval
import CertIMP.Transformation.Exercises

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
  induction a generalizing pre suf stack with
  | ANum n =>
      simp only [compile]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
  | AId x =>
      simp only [compile]
      apply Reachable.step
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
  | APlus a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ ADD :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]
  | AMinus a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ SUB :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]
  | AMult a1 a2 ih1 ih2 =>
      simp only [List.length_append] at ih2
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans ih1
      rw [List.length_append, ←List.append_assoc]
      apply @Reachable.trans _ _ (.ok {
          code := pre ++ a1.compile ++ (a2.compile ++ MUL :: suf),
          stack := eval mem a2 :: eval mem a1 :: stack,
          mem := mem,
          pc := pre.length + a1.compile.length + a2.compile.length
        })
      · rw [←List.length_append]
        apply ih2
      · apply Reachable.step
        rw [step, fetchInstr]
        simp [←Nat.add_assoc]
        have : pre.length + a1.compile.length + a2.compile.length <
          pre.length + a1.compile.length + a2.compile.length + suf.length + 1 := by omega
        simp [this, ←List.append_assoc, stackPeek2, replaceStackAndIncrPC, incrPC]

lemma BExp.compileCorrectAux {pre suf stack mem} (b : BExp) :
  Reachable
    (.ok ⟨pre ++ (b.compile ++ suf), stack, mem, pre.length⟩)
    (.ok ⟨pre ++ (b.compile ++ suf), (b.eval mem).toValue :: stack, mem, (pre ++ b.compile).length⟩) := by
    induction b generalizing pre suf stack with
    | BTrue =>
      apply Reachable.step
      simp only [compile]
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | BFalse =>
      apply Reachable.step
      simp only [compile]
      simp [step, fetchInstr, replaceStackAndIncrPC, incrPC]
    | BEq a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
          by_cases h : AExp.eval mem a1 = AExp.eval mem a2
          · simp +arith [h]
          · simp +arith [h]
            have : (AExp.eval mem a1 == AExp.eval mem a2) = false := by
              simp only [beq_eq_false_iff_ne]
              assumption
            simp only [this]
    | BNeq a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.trans (Reachable.step rfl)
          simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc, List.length_append,
            Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl,
            Nat.sub_self, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq]
          by_cases h : AExp.eval mem a1 = AExp.eval mem a2
          · simp +arith only [h, bne_self_eq_false]
            apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
          · simp +arith only [h]
            have : (AExp.eval mem a1 != AExp.eval mem a2) = true := by
              simp only [bne_iff_ne, ne_eq]
              assumption
            simp only [this]
            apply Reachable.step
            simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
    | BLe a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
          by_cases h : AExp.eval mem a1 ≤ AExp.eval mem a2 <;> simp +arith [h]
    | BGt a1 a2 =>
      simp only [compile, List.append_assoc, eval, List.length_append]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.trans
        · rw [←List.append_assoc]
          apply AExp.compileCorrectAux a2
        · apply Reachable.trans
          · apply Reachable.step
            rfl
          · simp only [step, Except.instMonad, Except.bind, fetchInstr, List.append_assoc, List.length_append,
              Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left, Nat.le_refl,
              Nat.sub_self, replaceStackAndIncrPC, incrPC, stackPeek2, beq_iff_eq]
            by_cases h : AExp.eval mem a1 ≤ AExp.eval mem a2
            · simp +arith only [h]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
              have h : (AExp.eval mem a2 < AExp.eval mem a1) = false := by
                simp only [Bool.false_eq_true, eq_iff_iff, iff_false, Nat.not_lt, h]
              simp only [h, Bool.false_eq_true, decide_false]
            · simp +arith only [h]
              apply Reachable.step
              simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek1, ←List.append_assoc]
              have : (AExp.eval mem a2 < AExp.eval mem a1) = true := by
                simp only [Nat.not_le] at h
                simp only [h]
              simp only [this, decide_true]
    | BNot b1 ih =>
        simp only [compile, List.append_assoc, eval, List.length_append]
        apply Reachable.trans
        · apply ih
        · apply Reachable.step
          simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2, stackPeek1]
          by_cases h : eval mem b1 = true <;> simp [h] <;> omega
    | BAnd b1 b2 ih1 ih2 =>
        simp only [compile, List.append_assoc, eval, List.length_append]
        apply Reachable.trans ih1
        rw [←List.append_assoc]
        apply Reachable.trans ih2
        apply Reachable.step
        simp [step, fetchInstr, replaceStackAndIncrPC, incrPC, stackPeek2]
        by_cases h1 : eval mem b1 = true <;> by_cases h2 : eval mem b2 = true
        all_goals
        simp only [h1, h2, Nat.mul_one, Bool.and_true, true_and, Bool.and_false]
        omega

/- For this proof, don't be set off if it becomes super technical and long.
   You can likely split the definition of Com.compileOffset into multiple sub-operations,
   and prove sub-lemmas for each sub-operation.
   But you don't have to; the naive way of proving this will likely suffice.
-/
lemma Com.compileCorrectAux (pgm σ σ' stack pre suf) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ, pre.length⟩)
    (.ok ⟨pre ++ pgm.compileOffset pre.length ++ suf, stack, σ', (pre ++ pgm.compileOffset pre.length).length⟩) := by
  induction h generalizing pre suf with
  | ESkip =>
      simp only [Com.compileOffset, List.append_assoc, List.cons_append, List.nil_append,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.step
      simp [step, fetchInstr, Except.instMonad, Except.bind, incrPC]
  | EAsgn h1 h2 =>
      subst h1
      subst h2
      simp only [Com.compileOffset, List.append_assoc, List.cons_append, List.nil_append,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply Reachable.trans
      · apply AExp.compileCorrectAux
      · apply Reachable.step
        simp [step, fetchInstr, Except.instMonad, Except.bind, stackPeek1, replaceMemStackAndIncrPC, replaceStackAndIncrPC, incrPC]
        rfl
  | ESeq c1 c2 ih1 ih2 =>
      simp only [Com.compileOffset, List.append_assoc, List.length_append]
      apply Reachable.trans
      · rw [←List.append_assoc]
        apply ih1
      · rename_i c₁ _ c₂ _
        specialize ih2 (pre ++ c₁.compileOffset pre.length) suf
        simp_all only [List.append_assoc, List.length_append]
  | EWhileTrue htrue h1 h2 ih1 ih2 =>
      rename_i c _ b _
      simp only [Com.compileOffset, List.append_assoc, List.cons_append, List.nil_append,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      apply Reachable.trans
      · apply BExp.compileCorrectAux
      · apply Reachable.trans
        · apply Reachable.step
          simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
          rfl
        · apply Reachable.trans
          · apply Reachable.step
            simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc,
              List.length_append, List.length_cons, Nat.reduceAdd, Nat.add_lt_add_iff_left,
              Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
              List.getElem_cons_succ, List.getElem_cons_zero, dite_eq_ite, replaceStackAndIncrPC,
              incrPC, beq_iff_eq, gt_iff_lt]
            simp only [← Nat.add_assoc, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceIte,
              stackPeek2, htrue, Nat.lt_add_one]
            rfl
          · apply Reachable.trans
            · specialize ih1 (pre ++ b.compile ++ [PUSH (pre.length + b.compile.length + 4),
              JUMPI, PUSH (pre.length + b.compile.length + (Com.compileOffset (pre.length + b.compile.length + 4) c).length + 6), JUMP]) (PUSH pre.length :: JUMP :: suf)
              simp_all only [List.append_assoc, List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
                Nat.reduceAdd, List.cons_append, List.nil_append]
              exact ih1
            · clear ih1
              simp only [Nat.add_assoc, Nat.reduceAdd]
              apply Reachable.trans
              · apply Reachable.step
                simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append,
                  List.length_cons, Nat.add_assoc, Nat.reduceAdd, Nat.add_lt_add_iff_left,
                  Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right,
                  List.getElem_append_right, Nat.add_sub_cancel_left, List.getElem_cons_succ,
                  Nat.le_refl, Nat.sub_self, List.getElem_cons_zero, replaceStackAndIncrPC, incrPC,
                  beq_iff_eq, gt_iff_lt]
                rfl
              · apply Reachable.trans
                · apply Reachable.step
                  simp [step, fetchInstr, Except.instMonad, Except.bind, Nat.add_assoc, stackPeek1]
                  rfl
                · simp only [Com.compileOffset, Nat.add_assoc, List.append_assoc, List.cons_append,
                  List.nil_append, List.length_append, List.length_cons, List.length_nil,
                  Nat.zero_add, Nat.reduceAdd] at ih2
                  apply ih2
  | EWhileFalse hfalse =>
      rename_i c b σ
      apply Reachable.trans
      · simp only [Com.compileOffset, List.append_assoc, List.cons_append, List.nil_append]
        apply BExp.compileCorrectAux
      · apply Reachable.trans
        · apply Reachable.step
          simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
          rfl
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
            simp [←Nat.add_assoc, hfalse]
            rfl
          · apply Reachable.trans
            · apply Reachable.step
              simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
              simp [←Nat.add_assoc]
              rfl
            · apply Reachable.step
              simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
              simp [←Nat.add_assoc, Com.compileOffset, stackPeek1]
  | EIfTrue htrue h ih =>
      rename_i σ c₁ σ' b c₂
      simp only [Com.compileOffset, Nat.add_assoc, List.append_assoc, List.cons_append,
        List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd]
      apply Reachable.trans
      · apply BExp.compileCorrectAux
      · apply Reachable.trans
        · apply Reachable.step
          simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
          rfl
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
            simp [←Nat.add_assoc, htrue]
            rfl
          · simp only [Nat.add_assoc, stackPeek2]
            apply Reachable.trans
            · specialize ih (pre ++ b.compile ++ [PUSH (pre.length + (b.compile.length + 4)),
              JUMPI, PUSH (pre.length + (b.compile.length + ((Com.compileOffset (pre.length + (b.compile.length + 4)) c₁).length + 6))), JUMP])
              aesop
            · clear ih
              apply Reachable.trans
              · apply Reachable.step
                simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
                rfl
              · apply Reachable.step
                simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
                simp [←Nat.add_assoc, stackPeek1]
  | EIfFalse hfalse h ih =>
      rename_i σ c₂ σ' b c₁
      simp only [Com.compileOffset, Nat.add_assoc, List.append_assoc, List.cons_append,
        List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd]
      apply Reachable.trans
      · apply BExp.compileCorrectAux
      · apply Reachable.trans
        · apply Reachable.step
          simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
          rfl
        · apply Reachable.trans
          · apply Reachable.step
            simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC, Nat.add_assoc]
            simp [←Nat.add_assoc, hfalse]
            rfl
          · simp only [Nat.add_assoc]
            apply Reachable.trans
            · apply Reachable.step
              simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
              rfl
            · apply Reachable.trans
              · apply Reachable.step
                simp [step, fetchInstr, Except.instMonad, Except.bind, Nat.add_assoc]
                simp [←Nat.add_assoc]
                rfl
              · apply Reachable.trans
                · simp [Nat.add_assoc, stackPeek1]
                  specialize ih <|
                    pre ++ b.compile ++
                      [PUSH (pre.length + (b.compile.length + 4)), JUMPI, PUSH (pre.length +
              (b.compile.length + ((Com.compileOffset (pre.length + (b.compile.length + 4)) c₁).length + 6))), JUMP] ++
                    (Com.compileOffset (pre.length + (b.compile.length + 4)) c₁) ++
                    [PUSH (pre.length +
                    (b.compile.length +
                      ((Com.compileOffset (pre.length + (b.compile.length + 4)) c₁).length +
                        ((Com.compileOffset
                              (pre.length +
                                (b.compile.length +
                                  ((Com.compileOffset (pre.length + (b.compile.length + 4)) c₁).length + 6)))
                              c₂).length +
                          8)))), JUMP]
                  aesop
                · clear ih
                  apply Reachable.trans
                  · apply Reachable.step
                    simp [step, fetchInstr, Except.instMonad, Except.bind, replaceStackAndIncrPC, incrPC]
                    rfl
                  · apply Reachable.step
                    simp only [step, Except.instMonad, Except.bind, fetchInstr, Nat.add_assoc,
                      Nat.reduceAdd, List.length_append, List.length_cons, Nat.add_lt_add_iff_left,
                      Nat.lt_add_left_iff_pos, Nat.zero_lt_succ, ↓reduceDIte, Nat.le_add_right,
                      List.getElem_append_right, Nat.add_sub_cancel_left, beq_iff_eq, gt_iff_lt]
                    simp only [← Nat.add_assoc, List.getElem_cons_succ]
                    simp [Nat.add_assoc, stackPeek1]

lemma Com.compileCorrectAux2 (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  Reachable
    (.ok ⟨pgm.compile, stack, σ, 0⟩)
    (.ok ⟨pgm.compile, stack, σ', pgm.compile.length⟩) := by
    rw [Com.compile]
    have hx := Com.compileCorrectAux _ σ σ' stack [] [STOP] h
    simp only [List.length_nil, List.nil_append] at hx
    apply Reachable.trans hx
    apply Reachable.step
    simp only [step, Except.instMonad, Except.bind, fetchInstr, List.length_append, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.lt_add_one, ↓reduceDIte, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
    List.getElem_cons_zero, replaceStackAndIncrPC, incrPC, stackPeek1, stackPeek2, beq_iff_eq, gt_iff_lt]

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

theorem Com.compileOptimizedCorrect (pgm σ σ' stack) (h : σ =[pgm]=> σ') :
  ∃ fuel : ℕ,
    execute fuel ⟨pgm.compileOptimized, stack, σ, 0⟩ = .ok ⟨pgm.compileOptimized, stack, σ', pgm.compileOptimized.length⟩ := by
  apply Com.compileCorrect
  rw [←fold_constants_com_sound]
  exact h
