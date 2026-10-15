import Tablet.Preamble

open scoped NNReal

-- [TABLET NODE: NearEqualFourGraphsParameters]
theorem NearEqualFourGraphsParameters (d₁₂ d₁₃ d₂₃ η : ENNReal)
    (h₁₂ : 0 < d₁₂) (h₁₂1 : d₁₂ ≤ 1)
    (h₁₃ : 0 < d₁₃) (h₁₃1 : d₁₃ ≤ 1)
    (h₂₃ : 0 < d₂₃) (h₂₃1 : d₂₃ ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ δ ζ e : ENNReal,
      0 < δ ∧ δ ≤ d₁₃ * d₂₃ ∧ δ ≤ η ∧ 32 * δ ≤ η ^ 5 ∧
      0 < ζ ∧ 0 < e ∧ e ≤ 1 ∧
      ∀ ε : ENNReal, ε ≤ e →
        ε ≤ δ ∧ ε ≤ η ∧ 2 * ε < d₁₂ ∧
        2 * ε < d₁₃ ∧ 2 * ε < d₂₃ ∧
        d₁₃ / 2 ≤ d₁₃ - ε ∧ d₂₃ / 2 ≤ d₂₃ - ε ∧
        (d₁₃ / 2) ^ 2 ≤ (d₁₃ - 2 * ε) ^ 2 ∧
        (d₂₃ / 2) ^ 2 ≤ (d₂₃ - 2 * ε) ^ 2 ∧
        d₁₃ * d₂₃ - δ ≤ (d₁₃ - ε) * (d₂₃ - ε) - ζ ∧
        (d₁₃ + ε) * (d₂₃ + ε) + ζ ≤ d₁₃ * d₂₃ + δ ∧
        (d₁₃ + 2 * ε) ^ 2 * (d₂₃ + 2 * ε) ^ 2 + ζ ≤
          (d₁₃ * d₂₃ + δ) ^ 2 := by
-- BODY
  lift d₁₂ to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top h₁₂1
  lift d₁₃ to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top h₁₃1
  lift d₂₃ to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top h₂₃1
  lift η to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top hη1
  norm_cast at h₁₂ h₁₂1 h₁₃ h₁₃1 h₂₃ h₂₃1 hη hη1
  let δ : ℝ≥0 := min (d₁₃ * d₂₃ / 8) (min (η / 4) (η ^ 5 / 128))
  let ζ : ℝ≥0 := min (δ / 4) (d₁₃ * d₂₃ * δ / 4)
  let e : ℝ≥0 := min (1 / 2) (min (δ / 8) (min (d₁₂ / 4)
    (min (d₁₃ / 8) (min (d₂₃ / 8) (d₁₃ * d₂₃ * δ / 64)))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hδq : δ ≤ d₁₃ * d₂₃ := by
    have h := min_le_left (d₁₃ * d₂₃ / 8) (min (η / 4) (η ^ 5 / 128))
    change δ ≤ _ at h
    rify at h ⊢
    nlinarith only [h, mul_nonneg d₁₃.coe_nonneg d₂₃.coe_nonneg]
  have hδη : δ ≤ η := by
    have h : δ ≤ η / 4 := (min_le_right _ _).trans (min_le_left _ _)
    rify at h ⊢
    nlinarith only [h, η.coe_nonneg]
  have hhier : 32 * δ ≤ η ^ 5 := by
    have h : δ ≤ η ^ 5 / 128 := (min_le_right _ _).trans (min_le_right _ _)
    rify at h ⊢
    nlinarith only [h, δ.coe_nonneg]
  have he1 : e ≤ 1 := by
    have h : e ≤ 1 / 2 := min_le_left _ _
    rify at h ⊢
    linarith only [h]
  refine ⟨(δ : ENNReal), (ζ : ENNReal), (e : ENNReal),
    by exact_mod_cast hδ, by exact_mod_cast hδq, by exact_mod_cast hδη,
    by exact_mod_cast hhier, by exact_mod_cast hζ, by exact_mod_cast he,
    by exact_mod_cast he1, ?_⟩
  intro ε hε
  lift ε to ℝ≥0 using ne_top_of_le_ne_top ENNReal.coe_ne_top hε
  norm_cast at hε ⊢
  obtain ⟨hεhalf, hεδ8, hε12, hε13, hε23, hεpoly⟩ :
      ε ≤ 1 / 2 ∧ ε ≤ δ / 8 ∧ ε ≤ d₁₂ / 4 ∧ ε ≤ d₁₃ / 8 ∧
      ε ≤ d₂₃ / 8 ∧ ε ≤ d₁₃ * d₂₃ * δ / 64 := by
    simpa only [e, le_min_iff] using hε
  have hεδ : ε ≤ δ := by
    rify at hεδ8 ⊢
    nlinarith only [hεδ8, δ.coe_nonneg]
  have hεη : ε ≤ η := hεδ.trans hδη
  have hεx : ε ≤ d₁₃ := by
    rify at hε13 ⊢
    nlinarith only [hε13, d₁₃.coe_nonneg]
  have hεy : ε ≤ d₂₃ := by
    rify at hε23 ⊢
    nlinarith only [hε23, d₂₃.coe_nonneg]
  have hε2x : 2 * ε ≤ d₁₃ := by
    rify at hε13 ⊢
    nlinarith only [hε13, d₁₃.coe_nonneg]
  have hε2y : 2 * ε ≤ d₂₃ := by
    rify at hε23 ⊢
    nlinarith only [hε23, d₂₃.coe_nonneg]
  have hζδ : ζ ≤ δ / 4 := min_le_left _ _
  have hζq : ζ ≤ d₁₃ * d₂₃ * δ / 4 := min_le_right _ _
  have hηR : (0 : ℝ) < η := by exact_mod_cast hη
  have hxR : (0 : ℝ) < d₁₃ := by exact_mod_cast h₁₃
  have hyR : (0 : ℝ) < d₂₃ := by exact_mod_cast h₂₃
  have hdR : (0 : ℝ) < d₁₂ := by exact_mod_cast h₁₂
  have hx1R : (d₁₃ : ℝ) ≤ 1 := by exact_mod_cast h₁₃1
  have hy1R : (d₂₃ : ℝ) ≤ 1 := by exact_mod_cast h₂₃1
  have hεhalfR : (ε : ℝ) ≤ 1 / 2 := by exact_mod_cast hεhalf
  have hεδ8R : (ε : ℝ) ≤ (δ : ℝ) / 8 := by exact_mod_cast hεδ8
  have hε12R : (ε : ℝ) ≤ (d₁₂ : ℝ) / 4 := by exact_mod_cast hε12
  have hε13R : (ε : ℝ) ≤ (d₁₃ : ℝ) / 8 := by exact_mod_cast hε13
  have hε23R : (ε : ℝ) ≤ (d₂₃ : ℝ) / 8 := by exact_mod_cast hε23
  have hεpolyR : (ε : ℝ) ≤ (d₁₃ : ℝ) * d₂₃ * δ / 64 := by exact_mod_cast hεpoly
  have hζδR : (ζ : ℝ) ≤ (δ : ℝ) / 4 := by exact_mod_cast hζδ
  have hζqR : (ζ : ℝ) ≤ (d₁₃ : ℝ) * d₂₃ * δ / 4 := by exact_mod_cast hζq
  refine ⟨hεδ, hεη, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rify
    linarith only [hdR, hε12R]
  · rify
    linarith only [hxR, hε13R]
  · rify
    linarith only [hyR, hε23R]
  · rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_sub hεx]
    linarith only [hε13R, hxR]
  · rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_sub hεy]
    linarith only [hε23R, hyR]
  · rw [← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_sub hε2x,
      NNReal.coe_mul, NNReal.coe_ofNat]
    have hh : (d₁₃ : ℝ) / 2 ≤ (d₁₃ : ℝ) - 2 * ε := by linarith only [hε13R, hxR]
    exact pow_le_pow_left₀ (by positivity) hh _
  · rw [← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_sub hε2y,
      NNReal.coe_mul, NNReal.coe_ofNat]
    have hh : (d₂₃ : ℝ) / 2 ≤ (d₂₃ : ℝ) - 2 * ε := by linarith only [hε23R, hyR]
    exact pow_le_pow_left₀ (by positivity) hh _
  · rw [← NNReal.coe_le_coe, NNReal.coe_sub hδq, NNReal.coe_mul,
      NNReal.coe_sub_def]
    apply le_max_of_le_left
    rw [NNReal.coe_mul, NNReal.coe_sub hεx, NNReal.coe_sub hεy]
    have ha := mul_nonneg (sub_nonneg.mpr hx1R) ε.coe_nonneg
    have hb := mul_nonneg (sub_nonneg.mpr hy1R) ε.coe_nonneg
    nlinarith only [ha, hb, hεδ8R, hζδR, sq_nonneg (ε : ℝ), δ.coe_nonneg]
  · rw [← NNReal.coe_le_coe]
    push_cast
    have ha := mul_nonneg (sub_nonneg.mpr hx1R) ε.coe_nonneg
    have hb := mul_nonneg (sub_nonneg.mpr hy1R) ε.coe_nonneg
    have hepsSq := mul_nonneg (sub_nonneg.mpr hεhalfR) ε.coe_nonneg
    nlinarith only [ha, hb, hepsSq, hεδ8R, hζδR, δ.coe_nonneg]
  · rw [← NNReal.coe_le_coe]
    push_cast
    have hepsSq := mul_nonneg (sub_nonneg.mpr hεhalfR) ε.coe_nonneg
    have hxPert : ((d₁₃ : ℝ) + 2 * ε) ^ 2 ≤ (d₁₃ : ℝ) ^ 2 + 6 * ε := by
      have h := mul_nonneg (sub_nonneg.mpr hx1R) ε.coe_nonneg
      nlinarith only [h, hepsSq]
    have hyPert : ((d₂₃ : ℝ) + 2 * ε) ^ 2 ≤ (d₂₃ : ℝ) ^ 2 + 6 * ε := by
      have h := mul_nonneg (sub_nonneg.mpr hy1R) ε.coe_nonneg
      nlinarith only [h, hepsSq]
    have hprod := mul_le_mul hxPert hyPert (sq_nonneg ((d₂₃ : ℝ) + 2 * ε))
      (by positivity : 0 ≤ (d₁₃ : ℝ) ^ 2 + 6 * ε)
    have hxSq : (d₁₃ : ℝ) ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ d₁₃.coe_nonneg hx1R 2
    have hySq : (d₂₃ : ℝ) ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ d₂₃.coe_nonneg hy1R 2
    have hxx := mul_nonneg (sub_nonneg.mpr hxSq) ε.coe_nonneg
    have hyy := mul_nonneg (sub_nonneg.mpr hySq) ε.coe_nonneg
    have hprodBound :
        ((d₁₃ : ℝ) + 2 * ε) ^ 2 * ((d₂₃ : ℝ) + 2 * ε) ^ 2 ≤
          ((d₁₃ : ℝ) * d₂₃) ^ 2 + 30 * ε := by
      nlinarith only [hprod, hxx, hyy, hepsSq]
    have hnonneg := mul_nonneg (mul_nonneg d₁₃.coe_nonneg d₂₃.coe_nonneg) δ.coe_nonneg
    nlinarith only [hprodBound, hεpolyR, hζqR, hnonneg, sq_nonneg (δ : ℝ)]
