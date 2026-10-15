import Tablet.LowerRegularPair

-- [TABLET NODE: LowerSuperRegularPair]
def LowerSuperRegularPair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (V₁ V₂ : Finset V) (ε d : ENNReal) : Prop :=
-- BODY
  LowerRegularPair G V₁ V₂ ε d ∧
  (∀ v ∈ V₁, (d - ε) * (V₂.card : ENNReal) ≤
    ((V₂.filter fun w => G.Adj v w).card : ENNReal)) ∧
  (∀ w ∈ V₂, (d - ε) * (V₁.card : ENNReal) ≤
    ((V₁.filter fun v => G.Adj v w).card : ENNReal))
