import Tablet.Preamble
import Mathlib.Analysis.SpecificLimits.Normed

-- [TABLET NODE: FourGraphsPolynomialLossAbsorption]
theorem FourGraphsPolynomialLossAbsorption (c : ENNReal) (hc : c < 1) :
    ∃ a₀ : ENNReal, 0 < a₀ ∧ ∀ a : ENNReal, 0 < a → a ≤ a₀ →
      ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ m : ℕ, n₀ ≤ m →
        (((m + 1 : ℕ) : ENNReal) + ((m + 1 : ℕ) : ENNReal) ^ 2) * c ^ m ≤
          (1 - a) ^ m := by
-- BODY
  have hcfin : c ≠ ⊤ := ne_top_of_lt hc
  have hcR : c.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hcfin ENNReal.one_ne_top).mpr hc
  let r : ℝ := (c.toReal + 1) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hcr : c.toReal < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hratio : c.toReal / r < 1 := (div_lt_one hr).mpr hcr
  have hratio0 : 0 ≤ c.toReal / r := div_nonneg ENNReal.toReal_nonneg hr.le
  have ht₀ := tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio
  have ht₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 hratio0 hratio
  have ht₂ := tendsto_pow_const_mul_const_pow_of_lt_one 2 hratio0 hratio
  have ht : Filter.Tendsto
      (fun m : ℕ => (((m : ℝ) + 1) + ((m : ℝ) + 1) ^ 2) * (c.toReal / r) ^ m)
      Filter.atTop (nhds 0) := by
    convert (ht₂.add (ht₁.const_mul 3)).add (ht₀.const_mul 2) using 1
    · ext m
      ring
    · norm_num
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨ENNReal.ofReal (1 - r), ENNReal.ofReal_pos.mpr (sub_pos.mpr hr1), ?_⟩
  intro a _ ha
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro m hm
  have hpoly : (((m : ℝ) + 1) + ((m : ℝ) + 1) ^ 2) * c.toReal ^ m ≤ r ^ m := by
    have h := (hN m (le_trans (le_max_right _ _) hm)).le
    rw [div_pow, ← mul_div_assoc] at h
    exact (div_le_one (pow_pos hr m)).mp h
  have hpolyE : (((m + 1 : ℕ) : ENNReal) + ((m + 1 : ℕ) : ENNReal) ^ 2) * c ^ m ≤
      ENNReal.ofReal r ^ m := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hcfin))
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_add (by simp : ((m + 1 : ℕ) : ENNReal) ≠ ⊤)
        (by finiteness : ((m + 1 : ℕ) : ENNReal) ^ 2 ≠ ⊤),
      ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      Nat.cast_add, Nat.cast_one] using hpoly
  have hrE : ENNReal.ofReal r ≤ 1 - a := by
    apply (ENNReal.le_sub_of_add_le_left
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha))
    calc
      a + ENNReal.ofReal r ≤ ENNReal.ofReal (1 - r) + ENNReal.ofReal r :=
        add_le_add ha le_rfl
      _ = 1 := by rw [← ENNReal.ofReal_add (sub_nonneg.mpr hr1.le) hr.le]; simp
  exact hpolyE.trans (pow_le_pow_left' hrE m)
