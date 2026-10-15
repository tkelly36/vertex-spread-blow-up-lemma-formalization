import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic

-- [TABLET NODE: LogFactorialBounds]
theorem LogFactorialBounds (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log n - n + Real.log n + 1 := by
-- BODY
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsR : 0 < (n : ℝ) + 1 := by positivity
    have hu := Real.log_le_sub_one_of_pos (div_pos hsR hnR)
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hsR hnR)
    rw [Real.log_div hsR.ne' hnR.ne'] at hu hl
    have hu' : (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hu hnR.le
      field_simp at this
      nlinarith
    have hl' : 1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
      have := mul_le_mul_of_nonneg_left hl hsR.le
      simp only [inv_div] at this
      field_simp at this
      nlinarith
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    constructor <;> nlinarith [ih.1, ih.2]
