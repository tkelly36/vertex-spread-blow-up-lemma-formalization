import Tablet.Preamble
import Mathlib.Data.Nat.Choose.Basic

-- [TABLET NODE: HypergeometricMass]
noncomputable def HypergeometricMass (n s t x : ℕ) : ℝ :=
-- BODY
  if x ≤ s then
    ((t.choose x : ℝ) * ((n - t).choose (s - x) : ℝ)) / (n.choose s : ℝ)
  else 0
