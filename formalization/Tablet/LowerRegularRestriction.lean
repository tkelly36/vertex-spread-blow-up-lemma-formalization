import Tablet.LowerRegularPair

-- [TABLET NODE: LowerRegularRestriction]
theorem LowerRegularRestriction {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W U' W' : Finset V)
    (ε θ d : ENNReal) (hU : U' ⊆ U) (hW : W' ⊆ W) (hεθ : ε ≤ θ)
    (hUthreshold : ε * (U.card : ENNReal) ≤ θ * (U'.card : ENNReal))
    (hWthreshold : ε * (W.card : ENNReal) ≤ θ * (W'.card : ENNReal))
    (hreg : LowerRegularPair G U W ε d) :
    LowerRegularPair G U' W' θ d := by
-- BODY
  intro S hS T hT hScard hTcard
  exact (tsub_le_tsub_left hεθ d).trans
    (hreg S (hS.trans hU) T (hT.trans hW)
      (hUthreshold.trans_lt hScard) (hWthreshold.trans_lt hTcard))
