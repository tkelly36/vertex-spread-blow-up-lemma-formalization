import Tablet.SuperRegularPair

-- [TABLET NODE: NearEqualRegularTriplet]
def NearEqualRegularTriplet {V : Type*} [Fintype V] [DecidableEq V]
    (F₁₂ F₁₃ F₂₃ : SimpleGraph V)
    [DecidableRel F₁₂.Adj] [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
    (W₁ W₂ W₃ : Finset V) (m : ℕ) (ε d₁₂ d₁₃ d₂₃ : ENNReal) : Prop :=
-- BODY
  W₁.card = m ∧ W₂.card = m ∧
  (W₃.card + 1 = m ∨ W₃.card = m ∨ W₃.card = m + 1) ∧
  Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₂ W₃ ∧
  SuperRegularPair F₁₂ W₁ W₂ ε d₁₂ ∧
  SuperRegularPair F₁₃ W₁ W₃ ε d₁₃ ∧
  SuperRegularPair F₂₃ W₂ W₃ ε d₂₃ ∧
  ∀ v ∈ W₁, ∀ u ∈ W₂, F₁₂.Adj v u →
    (d₁₃ * d₂₃ - ε) * W₃.card ≤
      ((W₃.filter fun z => F₁₃.Adj v z ∧ F₂₃.Adj u z).card : ENNReal) ∧
    ((W₃.filter fun z => F₁₃.Adj v z ∧ F₂₃.Adj u z).card : ENNReal) ≤
      (d₁₃ * d₂₃ + ε) * W₃.card
