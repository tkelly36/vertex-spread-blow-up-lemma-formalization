import Tablet.Preamble
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Permanent

open scoped BigOperators

-- [TABLET NODE: RowProductPolynomial]
noncomputable def RowProductPolynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
-- BODY
  ∏ i, ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j
