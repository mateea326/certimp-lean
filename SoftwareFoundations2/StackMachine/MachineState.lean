import SoftwareFoundations2.StackMachine.ISA

open Instruction AExp BExp

structure MachineState where
  code : List Instruction
  stack : Stack
  mem : State
  pc : ℕ
deriving Inhabited

inductive ExecutionException where
  | OutOfFuel
  | BadPC
  | BadStackLayout

/-
  Pretty-printing internals for machine state, you can ignore:
-/

def List.vars : List Instruction → List Var
  | [] => []
  | .LOAD x :: l => (x :: l.vars).dedup
  | .STORE x :: l => (x :: l.vars).dedup
  | _ :: l => l.vars

def mem_var_vals (code : List Instruction) (mem : State) : List (Var × Nat) :=
  List.foldr (fun x acc => ⟨x, mem x⟩ :: acc) [] code.vars

instance : Repr MachineState where
  reprPrec st _ :=
    .bracket "⟨"
      ( .line ++ "stack := " ++ repr st.stack ++ ", " ++
        .line ++ "code := " ++ repr st.code ++ ", " ++
        .line ++ "mem := " ++ repr (mem_var_vals st.code st.mem) ++ ", " ++
        .line ++ "pc := " ++ repr st.pc ++
        .line
      )
    "⟩"

instance : ToString ExecutionException where
  toString
    | .OutOfFuel => "out of fuel"
    | .BadPC => "bad program counter"
    | .BadStackLayout => "bad stack layout"
