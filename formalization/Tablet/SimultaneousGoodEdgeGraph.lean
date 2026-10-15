import Tablet.SuperRegularPair

-- [TABLET NODE: SimultaneousGoodEdgeGraph]
def SimultaneousGoodEdgeGraph {V K : Type*} [Fintype V] [DecidableEq V]
    [Fintype K] (F₁₂ : SimpleGraph V) (F₁₃ F₂₃ : K → SimpleGraph V)
    [DecidableRel F₁₂.Adj] [∀ k, DecidableRel (F₁₃ k).Adj]
    [∀ k, DecidableRel (F₂₃ k).Adj]
    (W₁ W₂ : Finset V) (_h₁₂ : Disjoint W₁ W₂) (W₃ : K → Finset V)
    (ε : K → ENNReal) (d₁₃ d₂₃ : K → ENNReal) : SimpleGraph V :=
-- BODY
  SimpleGraph.fromRel fun x v =>
    x ∈ W₁ ∧ v ∈ W₂ ∧ F₁₂.Adj x v ∧ ∀ k,
      (d₁₃ k * d₂₃ k - 2 * ε k) * (W₃ k).card ≤
        (((W₃ k).filter fun w => (F₁₃ k).Adj x w ∧ (F₂₃ k).Adj v w).card : ENNReal) ∧
      (((W₃ k).filter fun w => (F₁₃ k).Adj x w ∧ (F₂₃ k).Adj v w).card : ENNReal) ≤
        (d₁₃ k * d₂₃ k + 2 * ε k) * (W₃ k).card
