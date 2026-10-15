import Tablet.IndependentRetentionCount

-- [TABLET NODE: RetentionCountControl]
def RetentionCountControl {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (L R : Finset V) (q ξ : ℝ) (η : ENNReal)
    (ω : V × V → Bool) : Prop :=
-- BODY
  (∀ v ∈ L, let I := (({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2
    |(IndependentRetentionCount I ω : ℝ) - q * I.card| ≤ ξ * R.card) ∧
  (∀ w ∈ R, let I := (L.product {w}).filter fun p => G.Adj p.1 p.2
    |(IndependentRetentionCount I ω : ℝ) - q * I.card| ≤ ξ * L.card) ∧
  (∀ U ⊆ L, ∀ W ⊆ R,
    η * (L.card : ENNReal) < (U.card : ENNReal) →
    η * (R.card : ENNReal) < (W.card : ENNReal) →
    let I := (U.product W).filter fun p => G.Adj p.1 p.2
    |(IndependentRetentionCount I ω : ℝ) - q * I.card| ≤ ξ * (U.card * W.card))
