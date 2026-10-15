import Tablet.SuperRegularCodegreeExceptionalBound

-- [TABLET NODE: RegularPairGoodCodegrees]
theorem RegularPairGoodCodegrees :
    ∀ {V : Type*} [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (n : ℕ) (ε d : ENNReal),
      U.card = n → W.card = n → 2 * ε < d →
      SuperRegularPair G U W ε d →
      (((W ×ˢ W).filter fun z =>
          let C := (U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card
          (C : ENNReal) < (d - 2 * ε) ^ 2 * n ∨
            (d + 2 * ε) ^ 2 * n < (C : ENNReal)).card : ENNReal) ≤
        2 * ε * n ^ 2 := by
-- BODY
  classical
  intro V _ G _ U W n ε d hU hW hε hsr
  by_cases hn : n = 0
  · have hWempty : W = ∅ := Finset.card_eq_zero.mp (hW.trans hn)
    simp only [hWempty, Finset.empty_product, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero, zero_le]
  simpa only [hW] using
    SuperRegularCodegreeExceptionalBound G U W n ε d hU hn hε hsr
