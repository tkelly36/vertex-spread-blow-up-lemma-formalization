import Tablet.Preamble
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: FiniteIndependentSubgaussianTail]
theorem FiniteIndependentSubgaussianTail
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι)
    (hi : iIndepFun X μ)
    (hs : ∀ i ∈ s, HasSubgaussianMGF (X i) (1 / 4) μ)
    (N t : ℝ) (hN : 0 < N) (hr : (s.card : ℝ) ≤ N) (ht : 0 ≤ t) :
    μ.real {ω | t < |∑ i ∈ s, X i ω|} ≤
      2 * Real.exp (-2 * t ^ 2 / N) := by
-- BODY
  classical
  by_cases hz : s = ∅
  · subst s
    simp only [Finset.sum_empty, abs_zero, not_lt.mpr ht, Set.setOf_false,
      measureReal_empty]
    positivity
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hi hs
  let c : ℝ≥0 := ⟨N / 4, by positivity⟩
  have hc : ((∑ _i ∈ s, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ) ≤ (c : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    change (s.card : ℝ) * (1 / 4) ≤ N / 4
    linarith
  have hbig : HasSubgaussianMGF (fun ω => ∑ i ∈ s, X i ω) c μ := by
    refine ⟨hsum.integrable_exp_mul, fun u => ?_⟩
    exact (hsum.mgf_le u).trans (Real.exp_le_exp.mpr (by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg u))
        (by norm_num)))
  have hupper := hbig.measure_ge_le ht
  have hlower := hbig.neg.measure_ge_le ht
  have hsub : {ω | t < |∑ i ∈ s, X i ω|} ⊆
      {ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -(∑ i ∈ s, X i ω)} := by
    intro ω hω
    change t < |∑ i ∈ s, X i ω| at hω
    rcases (lt_abs.mp hω) with hω | hω
    · exact Or.inl (le_of_lt hω)
    · exact Or.inr hω.le
  have hden : -t ^ 2 / (2 * (c : ℝ)) = -2 * t ^ 2 / N := by
    change -t ^ 2 / (2 * (N / 4)) = -2 * t ^ 2 / N
    field_simp
    <;> ring
  rw [hden] at hupper hlower
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (by simpa [two_mul] using add_le_add hupper hlower))
