import Tablet.LowerSuperRegularPair
import Tablet.LowerRegularPair
import Tablet.PairDensity
import Tablet.RegularPair
import Tablet.SuperRegularPair
import Tablet.SuperRegularExtractionParameters
import Tablet.PairDensityReal
import Tablet.SuperRegularInitialSample
import Tablet.SuperRegularTypicalCore
import Tablet.SuperRegularCoreSample
import Tablet.SuperRegularExceptionalRestoration

-- The partition input comes from szemeredi_regularity through SuperRegularInitialSample.

-- [TABLET NODE: SuperRegularSubgraph]
theorem SuperRegularSubgraph :
    ∀ ε' d : ENNReal, 0 < ε' → ε' < 1 → 0 < d → d < 1 →
      ∃ ε : ENNReal, ∃ n₀ : ℕ, 0 < ε ∧ ε < ε' ∧
        ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (n : ℕ),
          n₀ ≤ n → U.card = n → W.card = n → Disjoint U W →
          U ∪ W = Finset.univ →
          (∀ ⦃u v⦄, G.Adj u v →
            (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U)) →
          LowerSuperRegularPair G U W ε (d + ε) →
          ∃ G' : SimpleGraph V, ∃ _ : DecidableRel G'.Adj,
            G' ≤ G ∧ SuperRegularPair G' U W ε' (d ^ 2 / 2) := by
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
  obtain ⟨h, γ, α, ε, l, M, n₀, hh, hh100, hhc, hhη, h3, h4, hbudget,
    hγ, hγ1, hα, hαγ, hαγγ, hε, hεη, hεM,
    hl, hlM, hbound, hn₀, hMn₀, hmargin, hcuts⟩ :=
    SuperRegularExtractionParameters η.toReal d.toReal hηR hηR1 hdR hdR1
  refine ⟨ENNReal.ofReal ε, n₀, ENNReal.ofReal_pos.mpr hε, ?_, ?_⟩
  · exact (ENNReal.ofReal_lt_iff_lt_toReal hε.le hηfin).mpr hεη
  intro V _ _ G _ U W n hn hU hW hUW hcover hbip hlow
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < n₀) hn
  have hh1 : h < 1 := hh100.trans_lt (by norm_num)
  obtain ⟨hfloor, hcut₁, hcut₂, hcut₃, hcut₄⟩ := hcuts n hn
  have hlowR : LowerSuperRegularPair G U W (ENNReal.ofReal ε)
      (ENNReal.ofReal d.toReal + ENNReal.ofReal ε) := by
    simpa only [ENNReal.ofReal_toReal hdfin] using hlow
  rcases hlowR with ⟨hreg, hdegUen, hdegWen⟩
  have hcancel : ENNReal.ofReal d.toReal + ENNReal.ofReal ε - ENNReal.ofReal ε =
      ENNReal.ofReal d.toReal := ENNReal.add_sub_cancel_right (by simp)
  have hlower : ∀ A ⊆ U, ∀ B ⊆ W, ε * n < (A.card : ℝ) →
      ε * n < (B.card : ℝ) → d.toReal ≤ (G.edgeDensity A B : ℝ) := by
    intro A hAU B hBW hA hB
    have hApos : 0 < A.card := by
      have : (0 : ℝ) < A.card := lt_of_le_of_lt (by positivity) hA
      exact_mod_cast this
    have hBpos : 0 < B.card := by
      have : (0 : ℝ) < B.card := lt_of_le_of_lt (by positivity) hB
      exact_mod_cast this
    have hAen : ENNReal.ofReal ε * (U.card : ENNReal) < A.card := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      simpa only [hU, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
        ENNReal.toReal_natCast] using hA
    have hBen : ENNReal.ofReal ε * (W.card : ENNReal) < B.card := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
      simpa only [hW, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le,
        ENNReal.toReal_natCast] using hB
    obtain ⟨hfin, hreal, _⟩ := PairDensityReal G A B
      (Finset.card_pos.mp hApos) (Finset.card_pos.mp hBpos)
    have hb := hreg A hAU B hBW hAen hBen
    rw [hcancel] at hb
    have hr := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hb
    simpa only [ENNReal.toReal_ofReal hdR.le, hreal] using hr
  have hdegU : ∀ u ∈ U,
      d.toReal * n ≤ ((W.filter fun w => G.Adj u w).card : ℝ) := by
    intro u hu
    have hb := hdegUen u hu
    rw [hcancel, hW] at hb
    have hr := ENNReal.toReal_mono (by simp) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdR.le,
      ENNReal.toReal_natCast] using hr
  have hdegW : ∀ w ∈ W,
      d.toReal * n ≤ ((U.filter fun u => G.Adj u w).card : ℝ) := by
    intro w hw
    have hb := hdegWen w hw
    rw [hcancel, hU] at hb
    have hr := ENNReal.toReal_mono (by simp) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hdR.le,
      ENNReal.toReal_natCast] using hr
  obtain ⟨H, hHdec, hHG, hreserveU, hreserveW, hrectH⟩ :=
    SuperRegularInitialSample G U W n l M ε d.toReal h γ α hU hW hUW hcover
      hbip hl hlM (hMn₀.trans hn) hbound hε hdR hdR1 hh hγ hγ1 hα
      hαγ hαγγ hεM hmargin hcut₁ hcut₂ hlower hdegU hdegW
  letI := hHdec
  obtain ⟨U₀, W₀, hU₀, hW₀, hbadU, hbadW, hcoreU, hcoreW⟩ :=
    SuperRegularTypicalCore H U W n d.toReal h hnpos hh hh1 hU hW hrectH
  have hcoreRect : ∀ A ⊆ U₀, ∀ B ⊆ W₀,
      h * n < (A.card : ℝ) → h * n < (B.card : ℝ) →
      |(H.edgeDensity A B : ℝ) - d.toReal| < h / 2 := by
    intro A hA B hB
    exact hrectH A (hA.trans hU₀) B (hB.trans hW₀)
  obtain ⟨F, hFdec, hFH, hFsupport, hFdegU, hFdegW, hrectF⟩ :=
    SuperRegularCoreSample H U₀ W₀ n d.toReal h hnpos hdR hdR1 hh
      (hUW.mono hU₀ hW₀) (by simpa only [hU] using Finset.card_le_card hU₀)
      (by simpa only [hW] using Finset.card_le_card hW₀)
      hcoreU hcoreW hcoreRect hcut₃ hcut₄
  letI := hFdec
  have hc : 0 < d.toReal ^ 2 / 2 := by positivity
  have hc1 : d.toReal ^ 2 / 2 < 1 := by nlinarith only [hdR, hdR1]
  obtain ⟨G', hG'dec, hG'H, hG'sr⟩ :=
    SuperRegularExceptionalRestoration H F U W U₀ W₀ n (d.toReal ^ 2 / 2) h
      η.toReal hU hW hUW hcover (fun _ _ huv => hbip (hHG huv)) hU₀ hW₀
      hc hc1 hh hhc hηR hηR1 h3 h4 hbudget hfloor hbadU hbadW
      hreserveU hreserveW hFH hFsupport hFdegU hFdegW hrectF
  letI := hG'dec
  have htarget : ENNReal.ofReal (d.toReal ^ 2 / 2) = d ^ 2 / 2 := by
    apply (ENNReal.toReal_eq_toReal (by simp) (by finiteness)).mp
    simp only [ENNReal.toReal_ofReal hc.le, ENNReal.toReal_div,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  refine ⟨G', hG'dec, hG'H.trans hHG, ?_⟩
  simpa only [ENNReal.ofReal_toReal hηfin, htarget] using hG'sr
