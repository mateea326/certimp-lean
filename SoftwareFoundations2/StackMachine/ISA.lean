import SoftwareFoundations2.Eval.State

abbrev Value : Type := Nat
abbrev Stack : Type := List Value

inductive Instruction where
  /-- `PUSH`:   Push a value literal onto the stack. -/
  | PUSH (n : Value)
  /-- `LOAD`:   Load a variable from memory and push onto the stack. -/
  | LOAD (x : Var)
  /-- `STORE`:  Store the topmost stack value in memory addressed by variable. -/
  | STORE (x : Var)
  /-- `ADD`:    Add the two topmost stack values. -/
  | ADD
  /-- `SUB`:    Subtract the two topmost stack values. -/
  | SUB
  /-- `MUL`:    Multiply the two topmost stack values. -/
  | MUL
  /-- `EQ`:     Compare the two topmost stack values for equality. -/
  | EQ
  /-- `LE`:     Compare the two topmost stack values for less-than-equality. -/
  | LE
  /-- `ISZERO`: Check if topmost stack value is 0. -/
  | ISZERO
  /-- `JUMP`:   Unconditional jump to the address at the top of stack. -/
  | JUMP
  /-- `JUMP`:   Conditional jump to the address at the top of stack. Condition is second topmost. -/
  | JUMPI
  /-- `STOP`:   Terminate execution -/
  | STOP
  /-- `NOP`:    Do nothing ("no operation") -/
  | NOP
deriving Repr, BEq
