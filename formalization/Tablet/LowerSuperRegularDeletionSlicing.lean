import Tablet.LowerSuperRegularPair

-- [TABLET NODE: LowerSuperRegularDeletionSlicing]
theorem LowerSuperRegularDeletionSlicing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W DU DW : Finset V) (ε d ε' d' : ENNReal)
    (hDU : DU ⊆ U) (hDW : DW ⊆ W)
    (hSR : LowerSuperRegularPair G U W ε d)
    (hReg : LowerRegularPair G (U \ DU) (W \ DW) ε' d')
    (hU : (d' - ε') * ((W \ DW).card : ENNReal) ≤
      (d - ε) * (W.card : ENNReal) - (DW.card : ENNReal))
    (hW : (d' - ε') * ((U \ DU).card : ENNReal) ≤
      (d - ε) * (U.card : ENNReal) - (DU.card : ENNReal)) :
    LowerSuperRegularPair G (U \ DU) (W \ DW) ε' d' := by
-- BODY
  refine ⟨hReg, ?_, ?_⟩
  · intro u hu
    have hfilter : ((W \ DW).filter fun w => G.Adj u w) =
        (W.filter fun w => G.Adj u w) \ DW := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hcard : (W.filter fun w => G.Adj u w).card ≤
        ((W \ DW).filter fun w => G.Adj u w).card + DW.card := by
      rw [hfilter]
      exact Finset.card_le_card_sdiff_add_card
    have hcast : ((W.filter fun w => G.Adj u w).card : ENNReal) ≤
        (((W \ DW).filter fun w => G.Adj u w).card : ENNReal) +
          (DW.card : ENNReal) := by
      exact_mod_cast hcard
    exact hU.trans (tsub_le_iff_right.mpr
      ((hSR.2.1 u (Finset.mem_sdiff.mp hu).1).trans hcast))
  · intro w hw
    have hfilter : ((U \ DU).filter fun v => G.Adj v w) =
        (U.filter fun v => G.Adj v w) \ DU := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hcard : (U.filter fun v => G.Adj v w).card ≤
        ((U \ DU).filter fun v => G.Adj v w).card + DU.card := by
      rw [hfilter]
      exact Finset.card_le_card_sdiff_add_card
    have hcast : ((U.filter fun v => G.Adj v w).card : ENNReal) ≤
        (((U \ DU).filter fun v => G.Adj v w).card : ENNReal) +
          (DU.card : ENNReal) := by
      exact_mod_cast hcard
    exact hW.trans (tsub_le_iff_right.mpr
      ((hSR.2.2 w (Finset.mem_sdiff.mp hw).1).trans hcast))
