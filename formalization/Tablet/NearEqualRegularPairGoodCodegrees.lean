import Tablet.SuperRegularCodegreeExceptionalBound

-- [TABLET NODE: NearEqualRegularPairGoodCodegrees]
theorem NearEqualRegularPairGoodCodegrees :
    ∀ {V : Type*} [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (m : ℕ) (ε d : ENNReal),
      U.card = m → (W.card + 1 = m ∨ W.card = m ∨ W.card = m + 1) →
      2 ≤ m → 2 * ε < d → SuperRegularPair G U W ε d →
      (((W ×ˢ W).filter fun z =>
          let C := (U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card
          (C : ENNReal) < (d - 2 * ε) ^ 2 * m ∨
            (d + 2 * ε) ^ 2 * m < (C : ENNReal)).card : ENNReal) ≤
        3 * ε * (W.card : ENNReal) ^ 2 := by
-- BODY
  classical
  intro V _ G _ U W m ε d hU _hm hm hε hsr
  exact (SuperRegularCodegreeExceptionalBound G U W m ε d hU
    (by omega) hε hsr).trans (by gcongr; norm_num)
