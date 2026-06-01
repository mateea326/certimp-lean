import CertIMP.Syntax

/-- A `machine state` (or just `state`) represents the current values
      of all variables at some point in the execution of a program.

    For simplicity, we make the following assumptions:
    - all variables are global;
    - variables only hold numbers;
    - the state is defined for _all_ variables, even though any given
      program is only able to mention a finite number of them.

    Because each variable stores a natural number, we can represent the state
      as a function from `Var` (which is an alias for `String`; i.e., variable names)
      to `Nat`, and will use `0` as default value in the store.
-/
def State : Type := Var → Nat

instance : Inhabited State where
  default := fun _ => 0

def State.init : State := Inhabited.default
def State.set (σ : State) (x : Var) (v : Nat) : State :=
  fun x' => if x' == x then v else σ x'

notation "·" => State.init
notation "[" x " ↦ " v "]" => State.set State.init x v
notation s "[" x " ↦ " v "]" => State.set s x v

@[grind =]
theorem State.set_comm {xn yn : Nat} (h : x ≠ y) : σ[x ↦ xn][y ↦ yn] = σ[y ↦ yn][x ↦ xn] := by
  unfold State.set
  funext str
  grind

@[grind =]
theorem State.set_id : σ[x ↦ σ x] = σ := by
  unfold State.set
  funext str
  grind
