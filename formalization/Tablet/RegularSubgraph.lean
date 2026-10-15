import Tablet.LowerRegularPair
import Tablet.RegularPair
import Tablet.PairDensity
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Tablet.RegularExtractionParameters
import Tablet.RegularExtractionPartitionGeometry
import Tablet.WeightedRectangleExpectation
import Tablet.SimultaneousUnequalRetention
import Tablet.PairDensityReal

-- [TABLET NODE: RegularSubgraph]
theorem RegularSubgraph :
    ∀ ε' d : ENNReal, 0 < ε' → ε' < 1 → 0 < d → d < 1 →
      ∃ ε : ENNReal, ∃ n₀ : ℕ, 0 < ε ∧ ε < ε' ∧
        ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (n : ℕ),
          n₀ ≤ n → U.card = n → W.card = n → Disjoint U W →
          U ∪ W = Finset.univ →
          (∀ ⦃u v⦄, G.Adj u v →
            (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U)) →
          LowerRegularPair G U W ε (d + ε) →
          ∃ G' : SimpleGraph V, ∃ _ : DecidableRel G'.Adj,
            G' ≤ G ∧ RegularPair G' U W ε' d := by
-- BODY
  classical
  intro η d hη hη1 hd hd1
  have hηfin : η ≠ ⊤ := ne_top_of_lt hη1
  have hdfin : d ≠ ⊤ := ne_top_of_lt hd1
  have hηR : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηfin
  have hdR : 0 < d.toReal := ENNReal.toReal_pos hd.ne' hdfin
  have hηR1 : η.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hηfin (by simp)).mpr hη1
  have hdR1 : d.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hdfin (by simp)).mpr hd1
  obtain ⟨h, γ, α, ε, l, M, n₀, hh, hhη, hh100, hγ, hγ1, hα,
    hαγ, hαγγ, hε, hεη, hεM, hl, hlM, hbound, hn₀, hMn₀, hmargin, hcut⟩ :=
    RegularExtractionParameters η.toReal hηR hηR1
  refine ⟨ENNReal.ofReal ε, n₀, ENNReal.ofReal_pos.mpr hε, ?_, ?_⟩
  · exact (ENNReal.ofReal_lt_iff_lt_toReal hε.le hηfin).mpr hεη
  intro V _ _ G _ U W n hn hU hW hUW hcover _ hlow
  have hMn : M ≤ n := hMn₀.trans hn
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < n₀) hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hV : Fintype.card V = n + n := by
    have hc := Finset.card_union_of_disjoint hUW
    rw [hcover, Finset.card_univ, hU, hW] at hc
    exact hc
  have hlV : l ≤ Fintype.card V := by rw [hV]; omega
  have hlower : ∀ A ⊆ U, ∀ B ⊆ W,
      ε * n < (A.card : ℝ) → ε * n < (B.card : ℝ) →
      d.toReal ≤ (G.edgeDensity A B : ℝ) := by
    intro A hAU B hBW hA hB
    have hApos : 0 < A.card := by
      have : (0 : ℝ) < A.card := (mul_pos hε hnr).trans hA
      exact_mod_cast this
    have hBpos : 0 < B.card := by
      have : (0 : ℝ) < B.card := (mul_pos hε hnr).trans hB
      exact_mod_cast this
    have hAen : ENNReal.ofReal ε * (U.card : ENNReal) < A.card := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      simpa only [hU, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
        ENNReal.toReal_natCast] using hA
    have hBen : ENNReal.ofReal ε * (W.card : ENNReal) < B.card := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      simpa only [hW, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
        ENNReal.toReal_natCast] using hB
    have hdens := PairDensityReal G A B (Finset.card_pos.mp hApos) (Finset.card_pos.mp hBpos)
    have hb := hlow A hAU B hBW hAen hBen
    rw [ENNReal.add_sub_cancel_right (by simp)] at hb
    rw [← hdens.2.1]
    exact (ENNReal.toReal_le_toReal hdfin hdens.1).mpr hb
  obtain ⟨P, heq, hlP, hPM, hunif⟩ := szemeredi_regularity G hα hlV
  have hPM' : P.parts.card ≤ M := hPM.trans hbound
  obtain ⟨_, E, hEP, _, hD, hslice, harea⟩ :=
    RegularExtractionPartitionGeometry G U W n l M ε d.toReal γ α hU hW hUW hcover
      hl hMn hε hdR hγ hγ1 hα hαγ hαγγ hεM hlower P heq hlP hPM' hunif
  obtain ⟨p, hp, hzero, _, _, _, hmeanAll⟩ :=
    WeightedRectangleExpectation G U W n l d.toReal γ α hU hW hdR hdR1.le
      hγ hα P E hEP hD hslice harea
  have hmean := hmeanAll h hh hmargin
  obtain ⟨H, hHdec, hHG, _, hsample⟩ :=
    SimultaneousUnequalRetention G U W n h hnpos hh hU hW hUW p hp hzero (hcut n hn)
  letI := hHdec
  refine ⟨H, hHdec, hHG, ?_⟩
  intro A hAU B hBW hA hB
  have hAR : η.toReal * n < (A.card : ℝ) := by
    have hc := (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hA
    simpa only [hU, ENNReal.toReal_mul, ENNReal.toReal_natCast] using hc
  have hBR : η.toReal * n < (B.card : ℝ) := by
    have hc := (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hB
    simpa only [hW, ENNReal.toReal_mul, ENNReal.toReal_natCast] using hc
  have hAh : h * n < (A.card : ℝ) :=
    (mul_lt_mul_of_pos_right hhη hnr).trans hAR
  have hBh : h * n < (B.card : ℝ) :=
    (mul_lt_mul_of_pos_right hhη hnr).trans hBR
  have hApos : (0 : ℝ) < A.card := (mul_pos hh hnr).trans hAh
  have hBpos : (0 : ℝ) < B.card := (mul_pos hh hnr).trans hBh
  have hareaPos : (0 : ℝ) < (A.card : ℝ) * B.card := mul_pos hApos hBpos
  have hm := hmean A hAU B hBW hAh hBh
  have hs := hsample A hAU B hBW hAh hBh
  have ht := abs_sub_le
    ((((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ))
    (∑ e ∈ A.product B, p e) (d.toReal * A.card * B.card)
  have herr : |(((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ) -
      d.toReal * A.card * B.card| < (h / 2) * A.card * B.card := by
    linarith only [hm, hs, ht]
  have hsmall : (h / 2) * A.card * B.card < η.toReal * A.card * B.card := by
    have : h / 2 < η.toReal := by linarith only [hh, hhη]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right this hApos) hBpos
  have hnonA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hnonB : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast hBpos)
  obtain ⟨hfinite, hreal, hquot⟩ := PairDensityReal H A B hnonA hnonB
  have hlo : d.toReal - η.toReal ≤ (PairDensity H A B).toReal := by
    rw [hreal, hquot]
    apply (le_div_iff₀ hareaPos).mpr
    have he := (abs_lt.mp herr).1
    nlinarith only [he, hsmall]
  have hhi : (PairDensity H A B).toReal ≤ d.toReal + η.toReal := by
    rw [hreal, hquot]
    apply (div_le_iff₀ hareaPos).mpr
    have he := (abs_lt.mp herr).2
    nlinarith only [he, hsmall]
  constructor
  · by_cases hηd : η ≤ d
    · apply (ENNReal.toReal_le_toReal (by finiteness) hfinite).mp
      simpa only [ENNReal.toReal_sub_of_le hηd hdfin] using hlo
    · simpa only [tsub_eq_zero_of_le (le_of_not_ge hηd)] using
        (zero_le (PairDensity H A B))
  · apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
    simpa only [ENNReal.toReal_add hdfin hηfin] using hhi
