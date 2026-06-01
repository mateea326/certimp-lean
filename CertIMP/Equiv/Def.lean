import CertIMP.Eval

namespace PgmEquiv

@[simp]
def aequiv (a₁ a₂ : AExp) : Prop :=
  ∀ σ : State, a₁.eval σ = a₂.eval σ

@[simp]
def bequiv (b₁ b₂ : BExp) : Prop :=
  ∀ σ : State, b₁.eval σ = b₂.eval σ

@[simp]
def cequiv (c₁ c₂ : Com) : Prop :=
  ∀ σ σ' : State, σ =[ c₁ ]=> σ' ↔ σ =[ c₂ ]=> σ'

scoped infix:100 " ≃ " => aequiv
scoped infix:100 " ≃ " => bequiv
scoped infix:100 " ≃ " => cequiv

end PgmEquiv
