import Tablet.Preamble
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

open MeasureTheory
open scoped NNReal

-- [TABLET NODE: IndependentEdgeSample]
noncomputable def IndependentEdgeSample (ι : Type*) [Fintype ι]
    (q : ℝ≥0) (hq : q ≤ 1) : Measure (ι → Bool) :=
-- BODY
  Measure.pi (fun _ : ι => (PMF.bernoulli q hq).toMeasure)
