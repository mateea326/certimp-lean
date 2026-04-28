import SoftwareFoundations2.StackMachine.MachineState

open Instruction AExp BExp

abbrev ExecutionState := Except ExecutionException MachineState

def stackPeek1 (μ : MachineState) : Except ExecutionException (Value × Stack) :=
  match μ.stack with
  | n1 :: s => .ok ⟨n1, s⟩
  | _       => .error .BadStackLayout

def stackPeek2 (μ : MachineState) : Except ExecutionException (Value × Value × Stack) :=
  match μ.stack with
  | n1 :: n2 :: s => .ok ⟨n1, n2, s⟩
  | _             => .error .BadStackLayout

def fetchInstr (μ : MachineState) : Except ExecutionException Instruction :=
  if _ : μ.pc < μ.code.length then
    .ok μ.code[μ.pc]
  else .error .BadPC

def incrPC (μ : MachineState) (pcΔ : ℕ := 1) : MachineState :=
  { μ with pc := μ.pc + pcΔ }

def replaceStackAndIncrPC (μ : MachineState) (s : Stack) (pcΔ : ℕ := 1) : MachineState :=
  incrPC { μ with stack := s } pcΔ

def replaceMemStackAndIncrPC
  (μ : MachineState) (mem : State) (s : Stack) (pcΔ : ℕ := 1) : MachineState :=
  replaceStackAndIncrPC { μ with mem := mem } s pcΔ

def step (μ : MachineState) : ExecutionState := do
  let instr ← fetchInstr μ
  match instr with
  | STOP     => .ok { μ with pc := μ.code.length }
  | PUSH n   =>
      .ok <| replaceStackAndIncrPC μ (n :: μ.stack)
  | LOAD x   =>
      .ok <| replaceStackAndIncrPC μ (μ.mem x :: μ.stack)
  | STORE x    =>
      let ⟨n1, s⟩ ← stackPeek1 μ
      .ok <| replaceMemStackAndIncrPC μ (μ.mem[x ↦ n1]) s
  | ADD      =>
      let ⟨n1, n2, s⟩ ← stackPeek2 μ
      .ok <| replaceStackAndIncrPC μ ((n2 + n1) :: s)
  | SUB      =>
      sorry
  | MUL      =>
      sorry
  | EQ       =>
      let ⟨n1, n2, s⟩ ← stackPeek2 μ
      if n2 == n1 then
        .ok <| replaceStackAndIncrPC μ (1 :: s)
      else
        .ok <| replaceStackAndIncrPC μ (0 :: s)
  | .LE       =>
      sorry
  | .ISZERO     =>
      sorry
  | JUMP =>
      let ⟨pc, s⟩ ← stackPeek1 μ
      .ok <| { μ with pc := pc, stack := s }
  | JUMPI =>
      let ⟨pc, b, s⟩ ← stackPeek2 μ
      if b > 0 then
        .ok <| { μ with pc := pc, stack := s }
      else
        .ok <| replaceStackAndIncrPC μ s
  | NOP => .ok <| incrPC μ

inductive Reachable : ExecutionState → ExecutionState → Prop where
  | step {μ st} : step μ = st → Reachable (.ok μ) st
  | trans {st1 st2 st'} : Reachable st1 st' → Reachable st' st2 → Reachable st1 st2

def isFinal : ExecutionState → Prop
  | .ok μ => μ.pc = μ.code.length
  | _     => False

def isError : ExecutionState → Prop
  | .error _ => True
  | _        => False

def outOfFuel : ExecutionState → Prop
  | .error .OutOfFuel => True
  | _                 => False

instance : Decidable (isFinal e) := by
  cases e
  · apply isFalse
    unfold isFinal
    simp only [not_false_eq_true]
  · next μ =>
    by_cases μ.pc = μ.code.length
    · apply isTrue
      unfold isFinal
      assumption
    · apply isFalse
      unfold isFinal
      assumption

def execute (fuel : ℕ) (μ : MachineState) : ExecutionState :=
  if isFinal (.ok μ) then
    .ok μ
  else match fuel with
  | 0 => .error .OutOfFuel
  | .succ fuel =>
      match step μ with
      | .ok μ => execute fuel μ
      | err   => err

def execute! (fuel : ℕ) (μ : MachineState) : MachineState :=
  match execute fuel μ with
  | .ok e' => e'
  | .error e => panic! s!"Execution failed with reason: {e}"

/-
  Uncomment after filling sorries above:

#eval execute! 1000 {
  stack     := [],
  code  := [PUSH 0, PUSH 1, MUL, PUSH 6, ADD, LOAD "x", MUL, PUSH 900, LE],
  pc    := 0,
  mem   := [ "x" ↦ 161 ],
}
-/
