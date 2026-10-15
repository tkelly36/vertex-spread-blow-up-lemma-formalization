import Tablet.PairDensity

-- [TABLET NODE: RegularPair]
def RegularPair {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (V₁ V₂ : Finset V) (ε d : ENNReal) : Prop :=
-- BODY
  ∀ U ⊆ V₁, ∀ W ⊆ V₂,
    ε * (V₁.card : ENNReal) < (U.card : ENNReal) →
    ε * (V₂.card : ENNReal) < (W.card : ENNReal) →
      d - ε ≤ PairDensity G U W ∧ PairDensity G U W ≤ d + ε
