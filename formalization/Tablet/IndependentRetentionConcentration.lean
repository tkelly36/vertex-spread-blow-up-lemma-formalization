import Tablet.IndependentEdgeSample
import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.IndependentRetentionCount

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: IndependentRetentionConcentration]
theorem IndependentRetentionConcentration {ι : Type*} [Fintype ι]
    (q : ℝ≥0) (hq : q ≤ 1) (I : Finset ι) (m : ℕ)
    (hm : 0 < m) (hI : I.card ≤ m) (ξ : ℝ) (hξ : 0 < ξ) :
    IndependentEdgeSample ι q hq
      {ω | ξ * m < |(IndependentRetentionCount I ω : ℝ) - (q : ℝ) * I.card|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ξ ^ 2 * m)) := by
-- BODY
  classical
  have hlaw :
      IsProbabilityMeasure (IndependentEdgeSample ι q hq) ∧
      iIndepFun (fun i (ω : ι → Bool) => (if ω i then 1 else 0 : ℝ))
        (IndependentEdgeSample ι q hq) ∧
      (∀ i : ι, ∫ ω, (if ω i then 1 else 0 : ℝ) ∂(IndependentEdgeSample ι q hq) = q) ∧
      (∀ i : ι, HasSubgaussianMGF (fun ω : ι → Bool =>
        (if ω i then 1 else 0 : ℝ) - q) (1 / 4) (IndependentEdgeSample ι q hq)) := by
    simpa only [IndependentEdgeSample] using
      (IndependentUnequalEdgeSampleLaw (fun _ : ι => q) (fun _ => hq))
  obtain ⟨hμ, hi, _, hsg⟩ := hlaw
  let μ := IndependentEdgeSample ι q hq
  letI : IsProbabilityMeasure μ := hμ
  by_cases hk : I.card = 0
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hk
    have ht : 0 < ξ * (m : ℝ) := mul_pos hξ (by exact_mod_cast hm)
    simp [hIempty, IndependentRetentionCount, not_lt_of_ge ht.le]
  have hkpos : (0 : ℝ) < I.card := by exact_mod_cast Nat.pos_of_ne_zero hk
  let X := fun i (ω : ι → Bool) => (if ω i then 1 else 0 : ℝ) - q
  have hix : iIndepFun X μ := hi.comp (fun _ x => x - (q : ℝ))
    (fun _ => measurable_id.sub_const (q : ℝ))
  have hs : HasSubgaussianMGF (fun ω => ∑ i ∈ I, X i ω)
      (∑ _i ∈ I, (1/4 : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hix (fun i _ => hsg i)
  have hsum (ω : ι → Bool) :
      (∑ i ∈ I, X i ω) = (IndependentRetentionCount I ω : ℝ) - (q : ℝ) * I.card := by
    dsimp [X]
    rw [Finset.sum_sub_distrib]
    have hc : (∑ i ∈ I, (if ω i then 1 else 0 : ℝ)) = IndependentRetentionCount I ω := by
      exact Finset.sum_boole (fun i => ω i = true) I
    rw [hc, Finset.sum_const, nsmul_eq_mul, mul_comm (I.card : ℝ)]
  have hparam : (2 * ((∑ _i ∈ I, (1/4 : ℝ≥0)) : ℝ≥0)) = (I.card : ℝ) / 2 := by
    norm_num [Finset.sum_const, nsmul_eq_mul]
    ring
  have ht : 0 ≤ ξ * (m : ℝ) := (mul_pos hξ (by exact_mod_cast hm)).le
  have hp := hs.measure_ge_le ht
  have hn := hs.neg.measure_ge_le ht
  rw [hparam] at hp hn
  let E := {ω : ι → Bool | ξ * m < |(IndependentRetentionCount I ω : ℝ) - (q : ℝ) * I.card|}
  let A := {ω : ι → Bool | ξ * m ≤ ∑ i ∈ I, X i ω}
  let B := {ω : ι → Bool | ξ * m ≤ -(∑ i ∈ I, X i ω)}
  have hsub : E ⊆ A ∪ B := by
    intro ω hω
    have hh : ξ * (m : ℝ) < |∑ i ∈ I, X i ω| := by simpa only [hsum] using hω
    rcases lt_abs.mp hh with h | h
    · exact Or.inl h.le
    · exact Or.inr (by dsimp [B]; linarith)
  have hb : μ.real E ≤ 2 * Real.exp (-(ξ * m)^2 / ((I.card : ℝ) / 2)) := by
    calc
      μ.real E ≤ μ.real (A ∪ B) := measureReal_mono hsub
      _ ≤ μ.real A + μ.real B := measureReal_union_le _ _
      _ ≤ _ := by dsimp [A, B]; simpa only [Pi.neg_apply, two_mul] using add_le_add hp hn
  have hmr : (I.card : ℝ) ≤ m := by exact_mod_cast hI
  have hmm : (0 : ℝ) < m := by exact_mod_cast hm
  have hexp : -(ξ * (m : ℝ)) ^ 2 / ((I.card : ℝ) / 2) ≤ -2 * ξ ^ 2 * m := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (I.card : ℝ) / 2)).mpr
    have hc := mul_le_mul_of_nonneg_left hmr (by positivity : (0 : ℝ) ≤ 2 * ξ^2 * m)
    nlinarith
  have hfinal : μ.real E ≤ 2 * Real.exp (-2 * ξ ^ 2 * m) :=
    hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num))
  change μ E ≤ _
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hfinal
