import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- [TABLET NODE: NegativeExponentialQuadraticBound]
theorem NegativeExponentialQuadraticBound (l : ℝ) (hl : l ≤ 0) :
    Real.exp l - 1 - l ≤ l ^ 2 / 2 := by
-- BODY
  let q : ℝ → ℝ := fun x => x ^ 2 / 2 - Real.exp x + 1 + x
  have hd (x : ℝ) : HasDerivAt q (x + 1 - Real.exp x) x := by
    convert ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (Real.hasDerivAt_exp x)).add_const 1 |>.add (hasDerivAt_id x) using 1
    simp
    ring
  have hanti : Antitone q := antitone_of_hasDerivAt_nonpos hd (by
    intro x
    change x + 1 - Real.exp x ≤ 0
    have := Real.add_one_le_exp x
    linarith)
  have h := hanti hl
  simp only [q, Real.exp_zero] at h
  nlinarith
