import Tablet.Preamble
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: IndependentUnequalEdgeSampleLaw]
theorem IndependentUnequalEdgeSampleLaw {ι : Type*} [Fintype ι]
    (q : ι → ℝ≥0) (hq : ∀ i, q i ≤ 1) :
    let μ := Measure.pi (fun i => (PMF.bernoulli (q i) (hq i)).toMeasure)
    IsProbabilityMeasure μ ∧
      iIndepFun (fun i (ω : ι → Bool) => (if ω i then 1 else 0 : ℝ)) μ ∧
      (∀ i, ∫ ω, (if ω i then 1 else 0 : ℝ) ∂μ = q i) ∧
      (∀ i, HasSubgaussianMGF (fun ω : ι → Bool =>
        (if ω i then 1 else 0 : ℝ) - q i) (1 / 4) μ) := by
-- BODY
  classical
  dsimp only
  let μ := Measure.pi (fun i => (PMF.bernoulli (q i) (hq i)).toMeasure)
  have hμ : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI := hμ
  have hi : iIndepFun (fun i (ω : ι → Bool) => (if ω i then 1 else 0 : ℝ)) μ := by
    exact iIndepFun_pi (fun _ =>
      (measurable_of_countable (fun b : Bool => (if b then 1 else 0 : ℝ))).aemeasurable)
  have he (i : ι) : ∫ ω, (if ω i then 1 else 0 : ℝ) ∂μ = q i := by
    have hp := measurePreserving_eval (fun i => (PMF.bernoulli (q i) (hq i)).toMeasure) i
    rw [← PMF.bernoulli_expectation (hq i), ← hp.map_eq]
    have hf : (fun b : Bool => (if b then 1 else 0 : ℝ)) =
        (fun b => cond b 1 0) := by ext b; cases b <;> rfl
    change (∫ ω, (if ω i then 1 else 0 : ℝ) ∂μ) = _
    rw [← hf]
    exact (integral_map (μ := μ) hp.measurable.aemeasurable
      (measurable_of_countable (fun b : Bool => (if b then 1 else 0 : ℝ))).aestronglyMeasurable).symm
  refine ⟨hμ, hi, he, ?_⟩
  intro i
  have hb : ∀ᵐ ω ∂μ, (if ω i then 1 else 0 : ℝ) ∈ Set.Icc 0 1 :=
    Filter.Eventually.of_forall (fun ω => by split <;> norm_num)
  have hs := hasSubgaussianMGF_of_mem_Icc
    (measurable_of_countable (fun ω : ι → Bool => (if ω i then 1 else 0 : ℝ))).aemeasurable hb
  norm_num [he i] at hs ⊢
  exact hs
