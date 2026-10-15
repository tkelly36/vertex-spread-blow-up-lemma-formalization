import Tablet.Preamble

-- [TABLET NODE: PairDensity]
noncomputable def PairDensity {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (U W : Finset V) : ENNReal :=
-- BODY
  (((U.product W).filter fun p : V × V => G.Adj p.1 p.2).card : ENNReal) /
    ((U.card : ENNReal) * (W.card : ENNReal))
