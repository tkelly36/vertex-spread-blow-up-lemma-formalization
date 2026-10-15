import Tablet.RegularPair

-- [TABLET NODE: SuperRegularPair]
def SuperRegularPair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (V₁ V₂ : Finset V) (ε d : ENNReal) : Prop :=
-- BODY
  RegularPair G V₁ V₂ ε d ∧
  (∀ v ∈ V₁,
    (d - ε) * (V₂.card : ENNReal) ≤
      ((V₂.filter fun w => G.Adj v w).card : ENNReal) ∧
    ((V₂.filter fun w => G.Adj v w).card : ENNReal) ≤
      (d + ε) * (V₂.card : ENNReal)) ∧
  (∀ w ∈ V₂,
    (d - ε) * (V₁.card : ENNReal) ≤
      ((V₁.filter fun v => G.Adj v w).card : ENNReal) ∧
    ((V₁.filter fun v => G.Adj v w).card : ENNReal) ≤
      (d + ε) * (V₁.card : ENNReal))
