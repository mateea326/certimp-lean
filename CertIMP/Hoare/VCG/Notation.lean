import CertIMP.Hoare.VCG.DCom
import Lean

open Lean Elab Term Meta PrettyPrinter

declare_syntax_cat dcom

syntax "skip"  : dcom
syntax ident " = " aexp : dcom
syntax dcom "; " : dcom
syntax dcom "; " dcom   : dcom
syntax "if " bexp " then " dcom " else " dcom " endif" : dcom
syntax "while " bexp "invariant " term:arg "do " dcom " od "  : dcom
syntax "{ " dcom " }" : dcom
syntax "{ " " }" : dcom
syntax "↑"term:arg " = " aexp : dcom
syntax "↑"term:arg : dcom

partial def elabDCom : Syntax → TermElabM Expr
  | `(dcom| skip)                          =>
        return .const ``DCom.DSkip []
  | `(dcom| $x:ident = $a)                 =>
        return mkAppN (.const ``DCom.DAsgn  []) #[mkStrLit <| identToString x, ← elabAExp a]
  | `(dcom| $c1 ; $c2)                     =>
        return mkAppN (.const ``DCom.DSeq   []) #[← elabDCom c1, ← elabDCom c2]
  | `(dcom| $c ;)                          => elabDCom c
  | `(dcom| if $b then $c1 else $c2 endif) =>
        return mkAppN (.const ``DCom.DIf    []) #[← elabBExp b, ← elabDCom c1, ← elabDCom c2]
  | `(dcom| while $b invariant $inv do $c od)             => do
        let i ← elabTerm inv (some (.const `Assertion []))
        return mkAppN (.const ``DCom.DWhile []) #[i, ← elabBExp b, ← elabDCom c]
  | `(dcom| { $c })                        => elabDCom c
  | `(dcom| { })                           =>
        return .const ``DCom.DSkip []
  | `(dcom| ↑$t:term = $a)                       => do
        let e ← elabTermEnsuringType t (some (.const `Var []))
        return mkAppN (.const ``DCom.DAsgn  []) #[e, ← elabAExp a]
  | `(dcom| ↑$t:term)                       => do
        let e ← elabTerm t (some (.const `Com []))
        return e
  | _                                     => throwUnsupportedSyntax

elab "decorated⟨{" pgm:dcom "}⟩"  : term => elabDCom pgm

/-
@[app_unexpander DCom.DSkip]
def unexpandDSkip : Unexpander
  | `($_) => `(dcom| skip)

@[app_unexpander Com.CAsgn]
def unexpandCAsgn : Unexpander
  | `($_ $x:str $a) => `(dcom| $(mkIdent x.getString.toName):ident = $(⟨a.raw⟩))
  | `($_ $x:ident $a) => `(dcom| $x:ident = $(⟨a.raw⟩))
  | _ => throw ()

@[app_unexpander Com.CSeq]
def unexpandCSeq : Unexpander
  | `($_ $c₁ $c₂) =>
      match c₂ with
      | `(dcom| $c₂ ; $c₃) =>
          `(dcom| $(⟨c₁.raw⟩) ; { $(⟨c₂.raw⟩) ; $(⟨c₃.raw⟩) } )
      | _ =>
          `(dcom| $(⟨c₁.raw⟩) ; $(⟨c₂.raw⟩))
  | _ => throw ()

@[app_unexpander Com.CIf]
def unexpandCIf : Unexpander
  | `($_ $b $c₁ $c₂) => `(dcom| if $(⟨b.raw⟩) then $(⟨c₁.raw⟩) else $(⟨c₂.raw⟩) endif)
  | _ => throw ()

@[app_unexpander Com.CWhile]
def unexpandCWhile : Unexpander
  | `($_ $b $c) => `(dcom| while $(⟨b.raw⟩) do $(⟨c.raw⟩) od)
  | _ => throw ()
-/
