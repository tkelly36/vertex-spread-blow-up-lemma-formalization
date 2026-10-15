import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- [TABLET NODE: BennettEntropyLowerBound]
theorem BennettEntropyLowerBound (z : ℝ) (hz : 0 ≤ z) :
    z ^ 2 / (2 * (1 + z / 3)) ≤ (1 + z) * Real.log (1 + z) - z := by
-- BODY
  let f : ℝ → ℝ := fun x => (1 + x) * Real.log (1 + x) - x -
    (3 / 2 : ℝ) * (x - 3 + 9 / (x + 3))
  let g : ℝ → ℝ := fun x => Real.log (1 + x) - 3 / 2 +
    27 / (2 * (x + 3) ^ 2)
  let g' : ℝ → ℝ := fun x => 1 / (1 + x) - 27 / (x + 3) ^ 3
  have hdg (x : ℝ) (hx : 0 ≤ x) : HasDerivAt g (g' x) x := by
    have h1 : 1 + x ≠ 0 := by linarith
    have h3 : x + 3 ≠ 0 := by linarith
    have ha := (hasDerivAt_id x).const_add 1
    have hb := ((hasDerivAt_id x).add_const 3).pow 2 |>.const_mul 2
    convert ((ha.log h1).sub_const (3 / 2)).add
      ((hasDerivAt_const x (27 : ℝ)).div hb
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 h3))) using 1
    dsimp [g']
    field_simp
    ring
  have hdf (x : ℝ) (hx : 0 ≤ x) : HasDerivAt f (g x) x := by
    have h1 : 1 + x ≠ 0 := by linarith
    have h3 : x + 3 ≠ 0 := by linarith
    have ha := (hasDerivAt_id x).const_add 1
    have hb := (hasDerivAt_id x).add_const 3
    convert ((ha.mul (ha.log h1)).sub (hasDerivAt_id x)).sub
      ((((hasDerivAt_id x).sub_const 3).add
        ((hasDerivAt_const x (9 : ℝ)).div hb h3)).const_mul (3 / 2)) using 1
    dsimp [g]
    field_simp
    ring
  have hg' (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g' x := by
    have h1 : 0 < 1 + x := by linarith
    have h3 : 0 < x + 3 := by linarith
    dsimp [g']
    rw [sub_nonneg, div_le_div_iff₀ (pow_pos h3 3) h1]
    nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  have hgmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro x hx
      exact (hdg x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hdg x (le_of_lt (by simpa using hx))).hasDerivWithinAt
    · intro x hx
      exact hg' x (le_of_lt (by simpa using hx))
  have hg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g x := by
    have h := hgmono (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
    norm_num [g] at h
    exact h
  have hfmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro x hx
      exact (hdf x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hdf x (le_of_lt (by simpa using hx))).hasDerivWithinAt
    · intro x hx
      exact hg x (le_of_lt (by simpa using hx))
  have h := hfmono (show 0 ∈ Set.Ici (0 : ℝ) by simp) hz hz
  norm_num [f] at h
  have he : (3 / 2 : ℝ) * (z - 3 + 9 / (z + 3)) =
      z ^ 2 / (2 * (1 + z / 3)) := by
    have h3 : z + 3 ≠ 0 := by linarith
    have hden : 1 + z / 3 ≠ 0 := by linarith
    field_simp
    ring
  rw [he] at h
  linarith
