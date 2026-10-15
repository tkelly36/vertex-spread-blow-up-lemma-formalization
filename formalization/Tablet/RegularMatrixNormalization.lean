import Tablet.RowProductPolynomial
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

-- [TABLET NODE: RegularMatrixNormalization]
theorem RegularMatrixNormalization {n : ℕ} (k : ℕ) (hk : 0 < k)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = (k : ℝ))
    (hcol : ∀ j, ∑ i, A i j = (k : ℝ)) :
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j => A i j / k
    (∀ i j, 0 ≤ B i j) ∧ (∀ i, ∑ j, B i j = 1) ∧
    (∀ j, ∑ i, B i j = 1) ∧
    Matrix.permanent A = (k : ℝ) ^ n * Matrix.permanent B := by
-- BODY
  dsimp only
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  refine ⟨fun i j => div_nonneg (hA i j) (Nat.cast_nonneg _), ?_, ?_, ?_⟩
  · intro i
    rw [← Finset.sum_div, hrow, div_self hkR]
  · intro j
    rw [← Finset.sum_div, hcol, div_self hkR]
  · have hscale : (k : ℝ) • (fun i j => A i j / (k : ℝ)) = A := by
      ext i j
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_div_cancel₀ (A i j) hkR
    simpa only [Fintype.card_fin] using
      (Matrix.permanent_smul (fun i j => A i j / (k : ℝ)) (k : ℝ)).symm.trans
        (congrArg Matrix.permanent hscale) |>.symm
