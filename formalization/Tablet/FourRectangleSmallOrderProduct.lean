import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin

-- [TABLET NODE: FourRectangleSmallOrderProduct]
theorem FourRectangleSmallOrderProduct (κ D : ℝ) (n : ℕ) (y : Fin 4 → ℕ)
    (hκ : 0 < κ) (hκsmall : κ < 1 / 4) (hD : 0 < D) (hn : 0 < n)
    (hy : ∑ i, y i = n) :
    (∏ i, if κ * (n : ℝ) ≤ (y i : ℝ) then
      D ^ y i * ((y i).factorial : ℝ) else ((y i).factorial : ℝ)) ≤
      D ^ n * Real.exp (-3 * κ * (n : ℝ) * Real.log (min D 1)) *
        ∏ i, ((y i).factorial : ℝ) := by
-- BODY
  classical
  let r : Fin 4 → ℝ := fun i => if κ * (n : ℝ) ≤ (y i : ℝ) then 0 else y i
  have hsum : ∑ i, (y i : ℝ) = (n : ℝ) := by exact_mod_cast hy
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlarge : ∃ i, κ * (n : ℝ) ≤ (y i : ℝ) := by
    by_contra h
    have hi : ∀ i, (y i : ℝ) < κ * (n : ℝ) := by simpa using h
    have hh := Finset.sum_lt_sum (fun i _ => (hi i).le)
      ⟨0, Finset.mem_univ _, hi 0⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [hsum] at hh
    norm_num at hh
    nlinarith [mul_lt_mul_of_pos_right hκsmall hnR]
  obtain ⟨j, hj⟩ := hlarge
  have hrj : r j = 0 := by simp [r, hj]
  have hr (i : Fin 4) : 0 ≤ r i ∧ r i ≤ κ * (n : ℝ) := by
    dsimp [r]
    split_ifs with h
    · exact ⟨le_rfl, (mul_pos hκ hnR).le⟩
    · exact ⟨Nat.cast_nonneg _, (not_le.mp h).le⟩
  have hq : ∑ i, r i ≤ 3 * κ * (n : ℝ) := by
    have he : (Finset.univ.erase j : Finset (Fin 4)).card = 3 := by simp
    have hs := Finset.sum_le_sum (s := Finset.univ.erase j) (fun i _ => (hr i).2)
    rw [Finset.sum_const, he, nsmul_eq_mul] at hs
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hrj, add_zero]
    convert hs using 1
    ring
  have hprod : (∏ i, if κ * (n : ℝ) ≤ (y i : ℝ) then
      D ^ y i * ((y i).factorial : ℝ) else ((y i).factorial : ℝ)) =
      Real.exp (((n : ℝ) - ∑ i, r i) * Real.log D) *
        ∏ i, ((y i).factorial : ℝ) := by
    have hi (i : Fin 4) :
        (if κ * (n : ℝ) ≤ (y i : ℝ) then D ^ y i * ((y i).factorial : ℝ)
        else ((y i).factorial : ℝ)) =
        Real.exp (((y i : ℝ) - r i) * Real.log D) * ((y i).factorial : ℝ) := by
      dsimp [r]
      split_ifs with h
      · rw [sub_zero, Real.exp_nat_mul, Real.exp_log hD]
      · simp
    simp_rw [hi]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_mul,
      Finset.sum_sub_distrib, hsum]
  rw [hprod]
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
  have hpow : D ^ n = Real.exp ((n : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hD]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases hD1 : 1 ≤ D
  · rw [min_eq_right hD1, Real.log_one]
    have hl : 0 ≤ Real.log D := Real.log_nonneg hD1
    have hq0 : 0 ≤ ∑ i, r i := Finset.sum_nonneg fun i _ => (hr i).1
    nlinarith [mul_nonneg hq0 hl]
  · rw [min_eq_left (not_le.mp hD1).le]
    have hl : Real.log D ≤ 0 := Real.log_nonpos hD.le (not_le.mp hD1).le
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) hl]
