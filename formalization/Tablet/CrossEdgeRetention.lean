import Tablet.Preamble

-- [TABLET NODE: CrossEdgeRetention]
def CrossEdgeRetention {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (L R : Finset V) (ω : V × V → Bool) : SimpleGraph V :=
-- BODY
  { Adj := fun v w => G.Adj v w ∧
      ((v ∈ L ∧ w ∈ R ∧ ω (v, w) = true) ∨
       (w ∈ L ∧ v ∈ R ∧ ω (w, v) = true))
    symm := by
      intro v w h
      exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩
    loopless := by
      refine ⟨fun v h => ?_⟩
      exact G.loopless.irrefl v h.1 }
