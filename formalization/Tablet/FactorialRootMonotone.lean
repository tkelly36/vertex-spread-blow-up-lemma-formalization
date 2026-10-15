import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic

-- [TABLET NODE: FactorialRootMonotone]
theorem FactorialRootMonotone (m y : ℕ) (hm : 0 < m) (hmy : m ≤ y) :
    Real.rpow (m.factorial : ℝ) (m : ℝ)⁻¹ ≤
      Real.rpow (y.factorial : ℝ) (y : ℝ)⁻¹ := by
-- BODY
  have step (n : ℕ) (hn : 0 < n) :
      Real.rpow (n.factorial : ℝ) (n : ℝ)⁻¹ ≤
        Real.rpow ((n + 1).factorial : ℝ) ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfac : 0 ≤ (n.factorial : ℝ) := by positivity
    have hroot : 0 ≤ Real.rpow (n.factorial : ℝ) (n : ℝ)⁻¹ :=
      Real.rpow_nonneg hfac _
    have hbound : Real.rpow (n.factorial : ℝ) (n : ℝ)⁻¹ ≤ (n + 1 : ℕ) := by
      apply (Real.rpow_inv_le_iff_of_pos hfac (by positivity) hnR).2
      rw [Real.rpow_natCast]
      exact_mod_cast (Nat.factorial_le_pow n).trans
        (Nat.pow_le_pow_left (Nat.le_succ n) n)
    apply (Real.le_rpow_inv_iff_of_pos hroot (by positivity) (by positivity)).2
    have hpower : (Real.rpow (n.factorial : ℝ) (n : ℝ)⁻¹) ^ n =
        (n.factorial : ℝ) := Real.rpow_inv_natCast_pow hfac (Nat.ne_of_gt hn)
    rw [Real.rpow_natCast, pow_succ, hpower, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hbound hfac
  induction y, hmy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hmy ih => exact ih.trans (step y (hm.trans_le hmy))
