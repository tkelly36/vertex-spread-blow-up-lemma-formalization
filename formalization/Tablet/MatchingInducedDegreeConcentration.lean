import Tablet.MatchingInducedGraphIdentities
import Tablet.SuperRegularPair
import Tablet.PerfectMatching

-- [TABLET NODE: MatchingInducedDegreeConcentration]
theorem MatchingInducedDegreeConcentration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G F H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] [DecidableRel H.Adj]
    (U W Z : Finset V) (hUW : Disjoint U W) (m : ℕ)
    (ε x y δ ζ c : ENNReal)
    (μ : PMF {f : U → W // PerfectMatching G U W hUW f})
    (hm : 0 < m) (hU : U.card = m) (hW : W.card = m)
    (hF : SuperRegularPair F U Z ε x) (hH : SuperRegularPair H W Z ε y)
    (hS : x / 2 ≤ x - ε) (hT : y / 2 ≤ y - ε)
    (hlo : x * y - δ ≤ (x - ε) * (y - ε) - ζ)
    (hhi : (x + ε) * (y + ε) + ζ ≤ x * y + δ)
    (hconc : ∀ S T : Finset V, S ⊆ U → T ⊆ W →
      x / 2 * m ≤ S.card → y / 2 * m ≤ T.card →
      1 - c ^ m ≤ μ.toOuterMeasure {f |
        (S.card : ENNReal) * T.card / m - ζ * m ≤
          ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ∧
        ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ≤
          (S.card : ENNReal) * T.card / m + ζ * m}) :
    1 - (Z.card : ENNReal) * c ^ m ≤ μ.toOuterMeasure {f |
      let A := MatchingInducedGraph F H U W Z f.1
      letI : DecidableRel A.Adj := Classical.decRel _
      let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
      ∀ z : Z,
        (x * y - δ) * m ≤ ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ∧
        ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ≤
          (x * y + δ) * m} := by
-- BODY
  classical
  let S (z : Z) := U.filter fun u => F.Adj u z
  let T (z : Z) := W.filter fun w => H.Adj w z
  let E (z : Z) : Set {f : U → W // PerfectMatching G U W hUW f} := {f |
    ((S z).card : ENNReal) * (T z).card / m - ζ * m ≤
      ((Finset.univ.filter fun u : U => u.1 ∈ S z ∧ (f.1 u).1 ∈ T z).card : ENNReal) ∧
    ((Finset.univ.filter fun u : U => u.1 ∈ S z ∧ (f.1 u).1 ∈ T z).card : ENNReal) ≤
      ((S z).card : ENNReal) * (T z).card / m + ζ * m}
  have hsizes (z : Z) :
      (x - ε) * m ≤ ((S z).card : ENNReal) ∧
      ((S z).card : ENNReal) ≤ (x + ε) * m ∧
      (y - ε) * m ≤ ((T z).card : ENNReal) ∧
      ((T z).card : ENNReal) ≤ (y + ε) * m := by
    have h₁ := hF.2.2 z z.property
    have h₂ := hH.2.2 z z.property
    exact ⟨by simpa only [hU] using h₁.1, by simpa only [hU] using h₁.2,
      by simpa only [hW] using h₂.1, by simpa only [hW] using h₂.2⟩
  have hE (z : Z) : 1 - c ^ m ≤ μ.toOuterMeasure (E z) := by
    exact hconc (S z) (T z) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      ((mul_le_mul_right' hS _).trans (hsizes z).1)
      ((mul_le_mul_right' hT _).trans (hsizes z).2.2.1)
  have htotal (B : Set {f : U → W // PerfectMatching G U W hUW f}) :
      μ.toOuterMeasure B + μ.toOuterMeasure Bᶜ = 1 := by
    as_aux_lemma =>
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ f, μ f := by
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : f ∈ B <;> simp [Set.indicator, hf]
      _ = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  have hfail (z : Z) : μ.toOuterMeasure (E z)ᶜ ≤ c ^ m := by
    have hle : μ.toOuterMeasure (E z) ≤ 1 := by
      rw [← htotal (E z)]
      exact le_self_add
    apply ENNReal.le_of_add_le_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
    rw [htotal (E z)]
    exact tsub_le_iff_right.mp (hE z)
  have hfailAll : μ.toOuterMeasure (⋂ z : Z, E z)ᶜ ≤ (Z.card : ENNReal) * c ^ m := by
    rw [Set.compl_iInter]
    calc
      _ ≤ ∑ z : Z, μ.toOuterMeasure (E z)ᶜ := MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ _z : Z, c ^ m := Finset.sum_le_sum (fun z _ => hfail z)
      _ = _ := by simp [nsmul_eq_mul]
  have hsuccess : 1 - (Z.card : ENNReal) * c ^ m ≤ μ.toOuterMeasure (⋂ z : Z, E z) := by
    apply tsub_le_iff_right.mpr
    rw [← htotal (⋂ z : Z, E z)]
    exact add_le_add le_rfl hfailAll
  refine hsuccess.trans (MeasureTheory.measure_mono ?_)
  intro f hf
  dsimp only
  intro z
  have hfz := Set.mem_iInter.mp hf z
  obtain ⟨_, _, _, _, _, hright, _⟩ := MatchingInducedGraphIdentities F H U W Z f.1
  rw [hright z]
  have hcard :
      (Finset.univ.filter fun u : U => F.Adj u z ∧ H.Adj (f.1 u) z).card =
      (Finset.univ.filter fun u : U => u.1 ∈ S z ∧ (f.1 u).1 ∈ T z).card := by
    congr 1
    ext u
    simp [S, T]
  rw [hcard]
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hcancel (a b : ENNReal) :
      (a * m) * (b * m) / m = (a * b) * m := by
    calc
      _ = ((a * b) * m) * m / m := by congr 1; ac_rfl
      _ = _ := ENNReal.mul_div_cancel_right hm0 (by simp)
  have hlowCenter : (x - ε) * (y - ε) * m ≤ ((S z).card : ENNReal) * (T z).card / m := by
    rw [← hcancel]
    exact ENNReal.div_le_div_right (mul_le_mul' (hsizes z).1 (hsizes z).2.2.1) _
  have hhighCenter : ((S z).card : ENNReal) * (T z).card / m ≤ (x + ε) * (y + ε) * m := by
    rw [← hcancel]
    exact ENNReal.div_le_div_right (mul_le_mul' (hsizes z).2.1 (hsizes z).2.2.2) _
  constructor
  · calc
      _ ≤ ((x - ε) * (y - ε) - ζ) * m := mul_le_mul_right' hlo _
      _ = ((x - ε) * (y - ε)) * m - ζ * m := ENNReal.sub_mul (by simp)
      _ ≤ ((S z).card : ENNReal) * (T z).card / m - ζ * m := tsub_le_tsub_right hlowCenter _
      _ ≤ _ := hfz.1
  · calc
      _ ≤ ((S z).card : ENNReal) * (T z).card / m + ζ * m := hfz.2
      _ ≤ ((x + ε) * (y + ε)) * m + ζ * m := add_le_add hhighCenter le_rfl
      _ = ((x + ε) * (y + ε) + ζ) * m := (add_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_right' hhi _
