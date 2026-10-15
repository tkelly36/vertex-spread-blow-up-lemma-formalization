import Tablet.Preamble

-- [TABLET NODE: PerfectMatching]
def PerfectMatching {V : Type*} [Fintype V] (G : SimpleGraph V) (U W : Finset V)
    (hUW : Disjoint U W) (f : U → W) : Prop :=
-- BODY
  Function.Bijective f ∧ ∀ u : U, G.Adj u (f u)
