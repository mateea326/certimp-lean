import CertIMP.Hoare.VCG.DCom
import CertIMP.Hoare.VCG.Notation
import Lean.Elab.Tactic

open Com DCom Hoare Proof
open Lean Elab Meta Tactic

def mkUndecorate (dec : Expr) := mkAppN (.const ``undecorate []) #[dec]
def mkAssertion : Expr := .const ``Assertion []
def mkAAnd (P Q : Expr) : Expr := mkAppN (.const ``Assertion.and []) #[P, Q]
def mkANeg (P : Expr) : Expr := mkAppN (.const ``Assertion.neg []) #[P]
def mkAImpl (P Q : Expr) : Expr := mkAppN (.const ``Assertion.impl []) #[P, Q]
def mkASubst (P x e : Expr) : Expr := mkAppN (.const ``Assertion.subst []) #[P, x, e]
def mkATrue (P : Expr) : Expr := mkAppN (.const ``Assertion.true []) #[P]
def mkBothElimL (P Q h : Expr) : Expr := mkAppN (.const ``Assertion.bothElimL []) #[P, Q, h]
def mkBothElimR (P Q h : Expr) : Expr := mkAppN (.const ``Assertion.bothElimR []) #[P, Q, h]
def mkAssert (b : Expr) : Expr := mkAppN (.const ``BExp.assert []) #[b]
def mkCSkip : Expr := .const ``CSkip []
def mkCAsgn (x e : Expr) : Expr := mkAppN (.const ``CAsgn []) #[x, e]
def mkCIf (b c1 c2 : Expr) : Expr := mkAppN (.const ``CIf []) #[b, c1, c2]
def mkCWhile (b c : Expr) : Expr := mkAppN (.const ``CWhile []) #[b, c]
def mkHSkip (P : Expr) : Expr := mkAppN (.const ``HSkip []) #[P]
def mkHAsgn (P x e : Expr) : Expr := mkAppN (.const ``HAsgn []) #[P, x, e]
def mkHSeq (Q d R P c pf2 pf1 : Expr) : Expr :=
  mkAppN (.const ``HSeq []) #[Q, d, R, P, c, pf2, pf1]
def mkHIf (P c1 Q c2 b pf1 pf2 : Expr) : Expr :=
  mkAppN (.const ``HIf []) #[P, c1, Q, c2, b, pf1, pf2]
def mkHWhile (c b P pf : Expr) : Expr :=
  mkAppN (.const ``HWhile []) #[c, b, P, pf]
def mkHConsequence (P' c Q' Q P pf impl1 impl2 : Expr) : Expr :=
  mkAppN (.const ``HConsequence []) #[P', c, Q', Q, P, pf, impl1, impl2]
def mkHPreStrengthen (P' c Q P pf impl : Expr) : Expr :=
  mkAppN (.const ``HPreStrengthen []) #[P', c, Q, P, pf, impl]
def mkDProof (preCon c postCon : Expr) : Expr :=
  mkAppN (.const ``DProof []) #[preCon, c, postCon]

partial def genVC (mvar : MVarId) : MetaM (List MVarId) :=
  mvar.withContext do
    let goal ← mvar.getType
    match goal.getAppFnArgs with
    | ⟨``DProof, #[preCon, pgm, postCon]⟩ =>
        match pgm.getAppFnArgs with
        | ⟨``DSkip, #[]⟩ =>
            if ← isDefEq preCon postCon then
              -- Base case for `skip`:
              -- precondition is equal to postcondition, so close goal by `HSkip`:
              mvar.assign <| mkHSkip postCon
              return []
            else
              -- Otherwise, apply `HPreStrengthen` on `HSkip` and turn goal to `preCon ->> postCon`
              let newGoal ← mkFreshExprMVar <| mkATrue <| mkAImpl preCon postCon
              mvar.assign <|
                mkHPreStrengthen postCon mkCSkip postCon preCon (mkHSkip postCon) newGoal
              return [newGoal.mvarId!]
        | ⟨``DAsgn, #[x, e]⟩ =>
            let newPreCon := mkASubst postCon x e
            if ← isDefEq preCon newPreCon then
              mvar.assign <| mkHAsgn postCon x e
              return []
            else
              -- Apply `HPreStrengthen` on `HAsgn` and rewrite goal to `preCon ->> postCon[e // x]`
              let newGoal ← mkFreshExprMVar <| mkATrue <| mkAImpl preCon newPreCon
              mvar.assign <| mkHPreStrengthen
                newPreCon (mkCAsgn x e) postCon preCon (mkHAsgn postCon x e) newGoal
              return [newGoal.mvarId!]
        | ⟨``DSeq, #[c1, c2]⟩ =>
            let midCon ← mkFreshExprMVar mkAssertion (userName:="MidAssertion".toName)
            let c2Goal ← mkFreshExprMVar <| mkDProof midCon c2 postCon
            let c1Goal ← mkFreshExprMVar <| mkDProof  preCon c1 midCon
            let unsolved := (← genVC c2Goal.mvarId!) ++ (← genVC c1Goal.mvarId!)
            mvar.assign <| mkHSeq
              midCon (mkUndecorate c2) postCon preCon (mkUndecorate c1) c2Goal c1Goal
            return unsolved ++ [midCon.mvarId!]
        | ⟨``DIf, #[b, c1, c2]⟩ =>
            let uc1 := mkUndecorate c1
            let uc2 := mkUndecorate c2
            let trueCon ← mkFreshExprMVar mkAssertion (userName:="TrueAssertion".toName)
            let falseCon ← mkFreshExprMVar mkAssertion (userName:="FalseAssertion".toName)
            let c1Goal ← mkFreshExprMVar <| mkDProof trueCon c1 postCon
            let c2Goal ← mkFreshExprMVar <| mkDProof falseCon c2 postCon
            let unsolved := (← genVC c1Goal.mvarId!) ++ (← genVC c2Goal.mvarId!)
            
            -- Compute the wp;
            -- Add wp /\ b -> trueCon, wp /\ ~b -> falseCon to proof obligations
            -- Use these obligations to apply pre-strenghtening to c1Goal and c2Goal
            -- (todo: all of this can be preproved)
            let wp := mkAAnd (mkAImpl (mkAssert b) trueCon)
                  (mkAImpl (mkANeg <| mkAssert b) falseCon)
            let str1 ← mkFreshExprMVar <| mkATrue (mkAImpl (mkAAnd wp (mkAssert b)) trueCon)
            let str2 ← mkFreshExprMVar <|
              mkATrue (mkAImpl (mkAAnd wp (mkANeg <| mkAssert b)) falseCon)
            let c1Strgth := mkHPreStrengthen
              trueCon uc1 postCon (mkAAnd wp (mkAssert b)) c1Goal str1
            let c2Strgth := mkHPreStrengthen
              falseCon uc2 postCon (mkAAnd wp (mkANeg <| mkAssert b)) c2Goal str2
            let ifPf := mkHIf wp uc1 postCon uc2 b c1Strgth c2Strgth
            
            -- If preCon is a metavariable, unify it with wp;
            -- else, add the preCon -> wp proof obligation
            if ← isDefEq preCon wp then
              mvar.assign ifPf
              return unsolved ++ [str1.mvarId!, str2.mvarId!]     
            else
              let str3 ← mkFreshExprMVar <| mkATrue (mkAImpl preCon wp)
              mvar.assign <| mkHPreStrengthen
                  wp (mkCIf b uc1 uc2) postCon preCon ifPf str3
              return unsolved ++ [str1.mvarId!, str2.mvarId!, str3.mvarId!]
        | ⟨``DWhile, #[inv, b, c]⟩ =>
            let cPre ← mkFreshExprMVar mkAssertion (userName:="PreAssertion".toName)
            let cGoal ← mkFreshExprMVar <| mkDProof cPre c inv
            let unsolved ← genVC cGoal.mvarId!

            -- inv ∧ b, inv ∧ ¬b
            let invAndB := mkAAnd inv <| mkAssert b
            let invAndNB := mkAAnd inv <| mkANeg <| mkAssert b
            -- inv ∧ b -> cPre 
            let impl1 := mkAImpl invAndB cPre
            -- preCon -> inv
            let impl2 := mkAImpl preCon inv
            -- inv ∧ ¬b -> postCon
            let impl3 := mkAImpl invAndNB postCon
            let newGoal ← mkFreshExprMVar <| mkATrue <| mkAAnd impl1 (mkAAnd impl2 impl3)
            -- proof of inv ∧ b -> cPre
            let cPreStrengthenPf := mkBothElimL impl1 (mkAAnd impl2 impl3) newGoal
            -- proof of preCon -> inv
            let rightPf := mkBothElimR impl1 (mkAAnd impl2 impl3) newGoal
            let invStrengthenPf := mkBothElimL impl2 impl3 rightPf
            -- proof of inv ∧ ¬b -> postCon
            let invWeakenPf := mkBothElimR impl2 impl3 rightPf
            
            let invPf := mkHPreStrengthen
                cPre (mkUndecorate c) inv invAndB cGoal cPreStrengthenPf
            let whilePf := mkHWhile (mkUndecorate c) b inv invPf
            mvar.assign <| mkHConsequence
                inv (mkCWhile b <| mkUndecorate c) invAndNB postCon preCon
                  whilePf invWeakenPf invStrengthenPf
            
            return [newGoal.mvarId!] ++ unsolved ++ [cPre.mvarId!]
        | _ => throwTacticEx `vcg mvar (m!"unknown syntax: {pgm}")
    | _ => throwTacticEx `vcg mvar (m!"expecting a Hoare triple as goal {goal}")

/-- `vcg` generates a `verification condition` from a decorated program and attempts to prove it. -/
elab "vcg" : tactic => do
  setGoals (← genVC (← getMainGoal))
  evalTactic (← `(tactic| try repeat verify_assertion))

namespace DCom

def skipVCG :
    DProof P decorated⟨{
                skip;
                while bfalse
                invariant P do
                    skip
                od;
                skip
             }⟩
          P := by
  vcg

def swap {n m : ℕ} :
  DProof ⦃ x = n ∧ y = m ⦄
      decorated⟨{
          x = x + y;
          y = x - y;
          x = x - y;
      }⟩
    ⦃ x = m ∧ y = n ⦄ := by
  vcg

def reduce_to_zero :
  DProof ⦃ ⊤ ⦄
      decorated⟨{
          while x != 0
          invariant ⦃ ⊤ ⦄ do
            x = x - 1;
          od
      }⟩
    ⦃ x = 0 ⦄ := by
  vcg

def if_minus_plus_dec :
  DProof ⦃ ⊤ ⦄
      decorated⟨{
          if (x <= y) then
            z = y - x;
          else
            y = x + z;
          endif
      }⟩
    ⦃ y = x + z ⦄ := by
  vcg

def subtract_slowly {m p : ℕ} :
  DProof ⦃ ⊤ ⦄
      decorated⟨{
          x = ↑m;
          z = ↑p;
          while x != 0
          invariant ⦃ z - x = p - m ⦄ do
            z = z - 1;
            x = x - 1;
          od
      }⟩
    ⦃ z = p - m ⦄ := by
  vcg

def slow_assignment {m : ℕ} :
  DProof ⦃ "x" = m ⦄
      decorated⟨{
          y = 0;
          while x != 0
          invariant ⦃ x + y = m ⦄ do
            x = x - 1;
            y = y + 1;
          od
      }⟩
    ⦃ "y" = m ⦄ := by
  vcg

end DCom
