import CertIMP.StackMachine.Semantics
import CertIMP.Transformation.ConstantFolding

open Instruction AExp BExp

def AExp.compile : AExp → List Instruction
  | ANum n       => [ PUSH n ]
  | AId x        => [ LOAD x ]
  | AMult a1 a2  => a1.compile ++ a2.compile ++ [ MUL ]
  | AMinus a1 a2 => a1.compile ++ a2.compile ++ [ SUB ]
  | APlus a1 a2  => a1.compile ++ a2.compile ++ [ ADD ]

def BExp.compile : BExp → List Instruction
  | BTrue        => [ PUSH 1 ]
  | BFalse       => [ PUSH 0 ]
  | BEq a1 a2    => a1.compile ++ a2.compile ++ [ EQ ]
  | BNeq a1 a2   => a1.compile ++ a2.compile ++ [ EQ, ISZERO ]
  | BLe a1 a2    => a1.compile ++ a2.compile ++ [ .LE ]
  | BGt a1 a2    => a1.compile ++ a2.compile ++ [ .LE, ISZERO ]
  | BNot b       => b.compile ++ [ISZERO]
  | BAnd b1 b2   => b1.compile ++ b2.compile ++ [ MUL ]

def Com.compileOffset (pcOffset : ℕ) : Com → List Instruction
  | CSkip       => [ NOP ]
  | CAsgn x a   => a.compile ++ [ STORE x ]
  | CSeq c1 c2  =>
      let c1c := c1.compileOffset pcOffset
      let c2c := c2.compileOffset (pcOffset + c1c.length)
      c1c ++ c2c
  | CIf b c1 c2 =>
      -- See comment below for stack layout
      let bCode := b.compile
      let pcJumpThen := pcOffset + bCode.length + 4
      let l1 := c1.compileOffset pcJumpThen
      let pcJumpElse := pcOffset + bCode.length + l1.length + 6
      let l2 := c2.compileOffset pcJumpElse
      let pcJumpPost := pcOffset + bCode.length + l1.length + l2.length + 8
      bCode ++ [ PUSH pcJumpThen, JUMPI, PUSH pcJumpElse, JUMP ] ++
        l1 ++ [ PUSH pcJumpPost, JUMP ] ++
        l2 ++ [ PUSH pcJumpPost, JUMP ]
  | CWhile b c  =>
      -- See comment below for stack layout
      let pcCheck := pcOffset
      let bCode := b.compile
      let pcJumpTrue := pcOffset + bCode.length + 4
      let l := c.compileOffset pcJumpTrue
      let pcJumpPost := pcOffset + bCode.length + l.length + 6
      bCode ++ [ PUSH pcJumpTrue, JUMPI, PUSH pcJumpPost, JUMP ] ++
        l ++ [ PUSH pcCheck, JUMP ]

def Com.compile (com : Com) := com.compileOffset 0 ++ [.STOP]

/-
  Code layout for a compiled `if b then l1 else l2`.
  First column: code section;
  Second column: offset within the code.

      bCode            pcOffset
      pcJumpThen       pcOffset + bCode.length
      JUMPI            pcOffset + bCode.length + 1
      pcJumpElse       pcOffset + bCode.length + 2
      JUMP             pcOffset + bCode.length + 3
      l1               pcOffset + bCode.length + 4                           { == pcJumpThen }
      pcJumpPost       pcOffset + bCode.length + l1.length + 4
      JUMP             pcOffset + bCode.length + l1.length + 5
      l2               pcOffset + bCode.length + l1.length + 6               { == pcJumpElse }
      pcJumpPost       pcOffset + bCode.length + l1.length + l2.length + 6
      JUMP             pcOffset + bCode.length + l1.length + l2.length + 7
                       pcOffset + bCode.length + l1.length + l2.length + 8   { == pcJumpPost }

  Code layout for a compiled `while b do l od`:

      bCode            pcOffset                                              { == pcCheck }
      pcJumpTrue       pcOffset + bCode.length
      JUMPI            pcOffset + bCode.length + 1
      pcJumpPost       pcOffset + bCode.length + 2
      JUMP             pcOffset + bCode.length + 3
      l                pcOffset + bCode.length + 4                           { == pcJumpTrue }
      pcCheck          pcOffset + bCode.length + l.length + 4
      JUMP             pcOffset + bCode.length + l.length + 5
                       pcOffset + bCode.length + l.length + 6                { == pcJumpPost }
-/

#eval aexp⟨{ (x * 2) - 1 + 30 }⟩.compile
#eval aexp⟨{ x - (2 * y) }⟩.compile
#eval ⟨{
    x = 10;
    while x > 0 do
      x = x - 1;
      if 6611 == 6611 then
        y = 6;
      else
        y = 0;
      endif
    od;
    y = x + 111;
  }⟩.compile
#eval ⟨{
      if x == 6 then
        y = x;
      else
        skip;
      endif;
      y = 0;
  }⟩.compile

#eval (execute! 1000 {
  stack     := [],
  code  := ⟨{
      if x == 6 then
        y = x;
      else
        skip;
      endif;
      y = 0;
  }⟩.compile,
  pc    := 0,
  mem   := [ "x" ↦ 6 ],
})
#eval (execute! 1000 {
  stack     := [],
  code  := ⟨{
    x = 10;
    while x > 0 do
      x = x - 1;
      if x == 6 then
        while x == 5 do
          skip
        od;
        y = x;
      else
        skip
      endif
    od;
    y = y + x + 111;
  }⟩.compile,
  pc    := 0,
  mem   := [ "x" ↦ 161 ],
})

def Com.compileOptimized (com : Com) := com.fold_constants.compile

#eval (execute! 1000 {
  stack     := [],
  code  := ⟨{
    x = 1 + 100 * 2;
  }⟩.compileOptimized,
  pc    := 0,
  mem   := State.init,
})
