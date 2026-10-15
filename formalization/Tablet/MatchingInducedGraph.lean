import Tablet.PerfectMatching

-- [TABLET NODE: MatchingInducedGraph]
def MatchingInducedGraph {V : Type*} [Fintype V] [DecidableEq V]
    (F₁₃ F₂₃ : SimpleGraph V) [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
    (W₁ W₂ W₃ : Finset V) (σ : W₁ → W₂) :
    SimpleGraph (W₁ ⊕ W₃) :=
-- BODY
  SimpleGraph.fromRel fun p q =>
    ∃ x : W₁, ∃ z : W₃, p = Sum.inl x ∧ q = Sum.inr z ∧
      F₁₃.Adj x z ∧ F₂₃.Adj (σ x) z
