import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- [TABLET NODE: MatchingConcentrationCorrection]
noncomputable def MatchingConcentrationCorrection (d ε : ℝ) : ℝ :=
-- BODY
  Real.log ((d + ε + 3 * Real.sqrt ε) / (d - 2 * ε)) -
    3 * Real.sqrt ε * Real.log (min (d + ε + 3 * Real.sqrt ε) 1)
