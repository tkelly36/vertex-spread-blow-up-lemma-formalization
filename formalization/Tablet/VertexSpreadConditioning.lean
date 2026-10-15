import Tablet.VertexSpreadOn

-- [TABLET NODE: VertexSpreadConditioning]
theorem VertexSpreadConditioning {X Y : Type*} {μ : PMF (X → Y)} {q p : ENNReal}
    {U : Set Y} (E : Set (X → Y)) (hE : ∃ f ∈ E, f ∈ μ.support)
    (hμ : VertexSpreadOn μ q U) (hp0 : 0 < p) (hp : p ≤ μ.toOuterMeasure E)
    (hratio : q / p ≤ 1) : VertexSpreadOn (μ.filter E hE) (q / p) U := by
-- BODY
  classical
  have hprob : ∀ (ν : PMF (X → Y)) (F : Set (X → Y)), ν.toOuterMeasure F ≤ 1 := by
    intro ν F
    calc
      ν.toOuterMeasure F ≤ ν.toOuterMeasure Set.univ :=
        ν.toOuterMeasure.mono (Set.subset_univ F)
      _ = 1 := (ν.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hp1 : p ≤ 1 := hp.trans (hprob μ E)
  have hfilter : ∀ F : Set (X → Y),
      (μ.filter E hE).toOuterMeasure F = μ.toOuterMeasure (F ∩ E) / μ.toOuterMeasure E := by
    intro F
    rw [PMF.toOuterMeasure_apply]
    calc
      (∑' f, F.indicator (μ.filter E hE) f) =
          ∑' f, (F ∩ E).indicator μ f * (μ.toOuterMeasure E)⁻¹ := by
        apply tsum_congr
        intro f
        by_cases hF : f ∈ F <;> by_cases hEf : f ∈ E <;>
          simp [PMF.filter_apply, PMF.toOuterMeasure_apply, hF, hEf]
      _ = (∑' f, (F ∩ E).indicator μ f) * (μ.toOuterMeasure E)⁻¹ :=
        ENNReal.tsum_mul_right
      _ = μ.toOuterMeasure (F ∩ E) / μ.toOuterMeasure E := by
        rw [← PMF.toOuterMeasure_apply, div_eq_mul_inv]
  refine ⟨hratio, ?_⟩
  intro s x y hx hy
  by_cases hs : s = 0
  · simpa only [hs, pow_zero] using hprob (μ.filter E hE) (CylinderEvent x y)
  · have hps : p ^ s ≤ p := by
      simpa only [pow_one] using
        pow_le_pow_right_of_le_one' hp1 (Nat.one_le_iff_ne_zero.2 hs)
    calc
      (μ.filter E hE).toOuterMeasure (CylinderEvent x y) =
          μ.toOuterMeasure (CylinderEvent x y ∩ E) / μ.toOuterMeasure E :=
        hfilter _
      _ ≤ q ^ s / p := ENNReal.div_le_div
        ((μ.toOuterMeasure.mono Set.inter_subset_left).trans (hμ.2 s x y hx hy)) hp
      _ ≤ q ^ s / p ^ s := ENNReal.div_le_div_left hps _
      _ = (q / p) ^ s := by
        simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
