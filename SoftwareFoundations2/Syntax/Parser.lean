import Lean
import SoftwareFoundations2.Syntax.AST

open Lean Elab Term Meta PrettyPrinter

declare_syntax_cat aexp
declare_syntax_cat bexp
declare_syntax_cat com

def identToString : Syntax → String := fun stx => stx.getId.toString

syntax num   : aexp
syntax ident : aexp
syntax:40 aexp:40 " + " aexp:41 : aexp
syntax:40 aexp:40 " - " aexp:41 : aexp
syntax:50 aexp:50 " * " aexp:51 : aexp
syntax:max "(" aexp ")" : aexp
syntax:max "↑"term:arg : aexp

syntax "btrue"  : bexp
syntax "bfalse"  : bexp
syntax aexp " == " aexp : bexp
syntax aexp " != " aexp : bexp
syntax aexp " <= " aexp : bexp
syntax aexp  " > " aexp : bexp
syntax "!" bexp : bexp
syntax bexp " && " bexp : bexp
syntax "(" bexp ")" : bexp
syntax "↑"term:arg : bexp

syntax "skip"  : com
syntax ident " = " aexp : com
syntax com "; " : com
syntax com "; " com   : com
syntax "if " bexp " then " com " else " com " endif" : com
syntax "while " bexp " do " com " od" : com
syntax "{ " com " }" : com
syntax "{ " " }" : com
syntax "↑"term:arg " = " aexp : com
syntax "↑"term:arg : com

partial def elabAExp : Syntax → TermElabM Expr
  | `(aexp| $n:num)    => return mkApp (.const ``AExp.ANum []) (mkNatLit n.getNat)
  | `(aexp| $x:ident)  => return mkApp (.const ``AExp.AId []) (mkStrLit <| identToString x)
  | `(aexp| $a1 + $a2) => return mkAppN (.const ``AExp.APlus  []) #[← elabAExp a1, ← elabAExp a2]
  | `(aexp| $a1 - $a2) => return mkAppN (.const ``AExp.AMinus []) #[← elabAExp a1, ← elabAExp a2]
  | `(aexp| $a1 * $a2) => return mkAppN (.const ``AExp.AMult  []) #[← elabAExp a1, ← elabAExp a2]
  | `(aexp| ( $a ))    => elabAExp a
  | `(aexp| ↑$t:term)                       => do
        let e ← elabTermEnsuringType t (some (.const `AExp []))
        return e
  | _                  => throwUnsupportedSyntax

partial def elabBExp : Syntax → TermElabM Expr
  | `(bexp| btrue)               =>
          return .const ``BExp.BTrue  []
  | `(bexp| bfalse)              =>
          return .const ``BExp.BFalse []
  | `(bexp| $a1:aexp == $a2) =>
          return mkAppN (.const ``BExp.BEq  []) #[← elabAExp a1, ← elabAExp a2]
  | `(bexp| $a1:aexp != $a2) =>
          return mkAppN (.const ``BExp.BNeq []) #[← elabAExp a1, ← elabAExp a2]
  | `(bexp| $a1:aexp <= $a2) =>
          return mkAppN (.const ``BExp.BLe  []) #[← elabAExp a1, ← elabAExp a2]
  | `(bexp| $a1:aexp > $a2)  =>
          return mkAppN (.const ``BExp.BGt  []) #[← elabAExp a1, ← elabAExp a2]
  | `(bexp| !$b)             =>
          return mkAppN (.const ``BExp.BNot []) #[← elabBExp b]
  | `(bexp| $b1 && $b2)     =>
          return mkAppN (.const ``BExp.BAnd []) #[← elabBExp b1, ← elabBExp b2]
  | `(bexp| ( $b ))         => elabBExp b
  | `(bexp| ↑$t:term)                       => do
        let e ← elabTerm t (some (.const `BExp []))
        return e
  | _                       => throwUnsupportedSyntax

partial def elabCom : Syntax → TermElabM Expr
  | `(com| skip)                          =>
        return .const ``Com.CSkip []
  | `(com| $x:ident = $a)                 =>
        return mkAppN (.const ``Com.CAsgn  []) #[mkStrLit <| identToString x, ← elabAExp a]
  | `(com| $c1 ; $c2)                     =>
        return mkAppN (.const ``Com.CSeq   []) #[← elabCom c1, ← elabCom c2]
  | `(com| $c ;)                          => elabCom c
  | `(com| if $b then $c1 else $c2 endif) =>
        return mkAppN (.const ``Com.CIf    []) #[← elabBExp b, ← elabCom c1, ← elabCom c2]
  | `(com| while $b do $c od)             =>
        return mkAppN (.const ``Com.CWhile []) #[← elabBExp b, ← elabCom c]
  | `(com| { $c })                        => elabCom c
  | `(com| { })                           =>
        return .const ``Com.CSkip []
  | `(com| ↑$t:term = $a)                       => do
        let e ← elabTermEnsuringType t (some (.const `Var []))
        return mkAppN (.const ``Com.CAsgn  []) #[e, ← elabAExp a]
  | `(com| ↑$t:term)                       => do
        let e ← elabTerm t (some (.const `Com []))
        return e
  | _                                     => throwUnsupportedSyntax

elab "aexp⟨{" exp:aexp "}⟩" : term => elabAExp exp
elab "bexp⟨{" exp:bexp "}⟩" : term => elabBExp exp
elab "⟨{" pgm:com "}⟩"  : term => elabCom pgm

@[app_unexpander AExp.ANum]
def unexpandANum : Unexpander
  | `($_ $n:num) => `(aexp| $n:num)
  | _ => throw ()

@[app_unexpander AExp.AId]
def unexpandAId : Unexpander
  | `($_ $x:str) => `(aexp| $(mkIdent x.getString.toName):ident)
  | _ => throw ()

@[app_unexpander AExp.APlus]
def unexpandAPlus : Unexpander
  | `($_ $a1 $a2) => `(aexp| $(⟨a1.raw⟩) + $(⟨a2.raw⟩))
  | _ => throw ()

@[app_unexpander AExp.AMinus]
def unexpandAMinus : Unexpander
  | `($_ $a1 $a2) => `(aexp| $(⟨a1.raw⟩) - $(⟨a2.raw⟩))
  | _ => throw ()

@[app_unexpander AExp.AMult]
def unexpandAMult : Unexpander
  | `($_ $a1 $a2) => `(aexp| $(⟨a1.raw⟩) * $(⟨a2.raw⟩))
  | _ => throw ()

@[app_unexpander BExp.BTrue]
def unexpandBTrue : Unexpander
  | `($_) => `(bexp| btrue)

@[app_unexpander BExp.BFalse]
def unexpandBFalse : Unexpander
  | `($_) => `(bexp| bfalse)

@[app_unexpander BExp.BEq]
def unexpandBEq : Unexpander
  | `($_ $a1 $a2) => `(bexp| $(⟨a1.raw⟩):aexp == $(⟨a2.raw⟩):aexp)
  | _ => throw ()

@[app_unexpander BExp.BNeq]
def unexpandBNeq : Unexpander
  | `($_ $a1 $a2) => `(bexp| $(⟨a1.raw⟩):aexp != $(⟨a2.raw⟩):aexp)
  | _ => throw ()

@[app_unexpander BExp.BLe]
def unexpandBLe : Unexpander
  | `($_ $a1 $a2) => `(bexp| $(⟨a1.raw⟩):aexp <= $(⟨a2.raw⟩):aexp)
  | _ => throw ()

@[app_unexpander BExp.BGt]
def unexpandBGt : Unexpander
  | `($_ $a1 $a2) => `(bexp| $(⟨a1.raw⟩):aexp > $(⟨a2.raw⟩):aexp)
  | _ => throw ()

@[app_unexpander BExp.BAnd]
def unexpandBAnd : Unexpander
  | `($_ $b1 $b2) => `(bexp| $(⟨b1.raw⟩):bexp && $(⟨b2.raw⟩):bexp)
  | _ => throw ()

@[app_unexpander BExp.BNot]
def unexpandBNot : Unexpander
  | `($_ $b1) => `(bexp| !$(⟨b1.raw⟩):bexp)
  | _ => throw ()

@[app_unexpander Com.CSkip]
def unexpandCSkip : Unexpander
  | `($_) => `(com| skip)

@[app_unexpander Com.CAsgn]
def unexpandCAsgn : Unexpander
  | `($_ $x:str $a) => `(com| $(mkIdent x.getString.toName):ident = $(⟨a.raw⟩))
  | `($_ $x:ident $a) => `(com| $x:ident = $(⟨a.raw⟩))
  | _ => throw ()

@[app_unexpander Com.CSeq]
def unexpandCSeq : Unexpander
  | `($_ $c₁ $c₂) =>
      match c₂ with
      | `(com| $c₂ ; $c₃) =>
          `(com| $(⟨c₁.raw⟩) ; { $(⟨c₂.raw⟩) ; $(⟨c₃.raw⟩) } )
      | _ =>
          `(com| $(⟨c₁.raw⟩) ; $(⟨c₂.raw⟩))
  | _ => throw ()

@[app_unexpander Com.CIf]
def unexpandCIf : Unexpander
  | `($_ $b $c₁ $c₂) => `(com| if $(⟨b.raw⟩) then $(⟨c₁.raw⟩) else $(⟨c₂.raw⟩) endif)
  | _ => throw ()

@[app_unexpander Com.CWhile]
def unexpandCWhile : Unexpander
  | `($_ $b $c) => `(com| while $(⟨b.raw⟩) do $(⟨c.raw⟩) od)
  | _ => throw ()
