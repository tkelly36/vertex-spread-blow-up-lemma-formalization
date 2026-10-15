import Tablet.Preamble

-- [TABLET NODE: ExposureDensityRecursion]
theorem ExposureDensityRecursion (d : ENNReal) (Delta : ℕ)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ p rho : ℕ → ENNReal,
      p 0 = d ∧
      (∀ x, x ≤ Delta → 0 < p x ∧ p x ≤ 1 ∧ 0 < rho x ∧ rho x < p x) ∧
      (∀ x, x < Delta → p (x + 1) = rho x * (d / 2)) ∧
      (∀ x, x < Delta → 0 < p x - p (x + 1)) := by
-- BODY
  let p : ℕ → ENNReal := fun x => d * (d / 4) ^ x
  let rho : ℕ → ENNReal := fun x => p x / 2
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd1
  have hquarter : d / 4 ≤ 1 := by
    calc
      d / 4 ≤ 1 / 4 := by gcongr
      _ ≤ 1 := by norm_num
  have hp (x : ℕ) : 0 < p x ∧ p x ≤ 1 := by
    refine ⟨ENNReal.mul_pos hd.ne' (ENNReal.pow_pos
      (ENNReal.div_pos hd.ne' (by norm_num)) x).ne', ?_⟩
    calc
      p x ≤ 1 * 1 ^ x := mul_le_mul' hd1 (pow_le_pow_left' hquarter x)
      _ = 1 := by simp
  have hrho (x : ℕ) : 0 < rho x ∧ rho x < p x := by
    have hptop : p x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hp x).2
    refine ⟨ENNReal.div_pos (hp x).1.ne' (by norm_num), ?_⟩
    apply (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hptop (by norm_num)) hptop).mp
    have hpr := ENNReal.toReal_pos (hp x).1.ne' hptop
    change (p x / 2).toReal < (p x).toReal
    rw [ENNReal.toReal_div]
    norm_num
    linarith
  have hrec (x : ℕ) : p (x + 1) = rho x * (d / 2) := by
    dsimp [p, rho]
    rw [pow_succ]
    simp only [div_eq_mul_inv]
    have hfour : (4 : ENNReal)⁻¹ = 2⁻¹ * 2⁻¹ := by
      rw [← ENNReal.mul_inv]
      all_goals norm_num
    rw [hfour]
    ring
  refine ⟨p, rho, by simp [p], ?_, fun x _ => hrec x, ?_⟩
  · intro x _
    exact ⟨(hp x).1, (hp x).2, (hrho x).1, (hrho x).2⟩
  · intro x _
    have hhalf : d / 2 ≤ 1 := by
      calc
        d / 2 ≤ 1 / 2 := by gcongr
        _ ≤ 1 := by norm_num
    have hdecrease : p (x + 1) < p x := by
      rw [hrec]
      have hle : rho x * (d / 2) ≤ rho x := by
        simpa using mul_le_mul_left' hhalf (rho x)
      exact hle.trans_lt (hrho x).2
    exact tsub_pos_iff_lt.mpr hdecrease
