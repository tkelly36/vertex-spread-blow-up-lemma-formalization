import Tablet.MatchingInducedGraphIdentities
import Tablet.PerfectMatching

-- [TABLET NODE: MatchingInducedCodegreeConcentration]
theorem MatchingInducedCodegreeConcentration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G F H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] [DecidableRel H.Adj]
    (U W Z : Finset V) (hUW : Disjoint U W) (m : ℕ)
    (ε x y δ ζ c : ENNReal)
    (μ : PMF {f : U → W // PerfectMatching G U W hUW f})
    (hm : 0 < m) (hU : U.card = m) (hW : W.card = m)
    (hS : (x / 2) ^ 2 ≤ (x - 2 * ε) ^ 2)
    (hT : (y / 2) ^ 2 ≤ (y - 2 * ε) ^ 2)
    (hwindow : (x + 2 * ε) ^ 2 * (y + 2 * ε) ^ 2 + ζ ≤ (x * y + δ) ^ 2)
    (hbadF : (((Z ×ˢ Z).filter fun z =>
      ((U.filter fun u => F.Adj u z.1 ∧ F.Adj u z.2).card : ENNReal) < (x - 2 * ε) ^ 2 * m ∨
      (x + 2 * ε) ^ 2 * m < ((U.filter fun u => F.Adj u z.1 ∧ F.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 3 * ε * (Z.card : ENNReal) ^ 2)
    (hbadH : (((Z ×ˢ Z).filter fun z =>
      ((W.filter fun u => H.Adj u z.1 ∧ H.Adj u z.2).card : ENNReal) < (y - 2 * ε) ^ 2 * m ∨
      (y + 2 * ε) ^ 2 * m < ((W.filter fun u => H.Adj u z.1 ∧ H.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 3 * ε * (Z.card : ENNReal) ^ 2)
    (hconc : ∀ S T : Finset V, S ⊆ U → T ⊆ W →
      (x / 2) ^ 2 * m ≤ S.card → (y / 2) ^ 2 * m ≤ T.card →
      1 - c ^ m ≤ μ.toOuterMeasure {f |
        (S.card : ENNReal) * T.card / m - ζ * m ≤
          ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ∧
        ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ≤
          (S.card : ENNReal) * T.card / m + ζ * m}) :
    1 - (Z.card : ENNReal) ^ 2 * c ^ m ≤ μ.toOuterMeasure {f |
      let A := MatchingInducedGraph F H U W Z f.1
      letI : DecidableRel A.Adj := Classical.decRel _
      let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
      let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
      (((R ×ˢ R).filter fun z =>
        (x * y + δ) ^ 2 * m <
          ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 6 * ε * (Z.card : ENNReal) ^ 2} := by
-- BODY
  classical
  let BF := (Z ×ˢ Z).filter fun z =>
    ((U.filter fun u => F.Adj u z.1 ∧ F.Adj u z.2).card : ENNReal) < (x - 2 * ε) ^ 2 * m ∨
    (x + 2 * ε) ^ 2 * m < ((U.filter fun u => F.Adj u z.1 ∧ F.Adj u z.2).card : ENNReal)
  let BH := (Z ×ˢ Z).filter fun z =>
    ((W.filter fun u => H.Adj u z.1 ∧ H.Adj u z.2).card : ENNReal) < (y - 2 * ε) ^ 2 * m ∨
    (y + 2 * ε) ^ 2 * m < ((W.filter fun u => H.Adj u z.1 ∧ H.Adj u z.2).card : ENNReal)
  let P := (Z ×ˢ Z) \ (BF ∪ BH)
  let S (z : P) := U.filter fun u => F.Adj u z.1.1 ∧ F.Adj u z.1.2
  let T (z : P) := W.filter fun u => H.Adj u z.1.1 ∧ H.Adj u z.1.2
  have hbounds (z : P) :
      (x - 2 * ε) ^ 2 * m ≤ ((S z).card : ENNReal) ∧
      ((S z).card : ENNReal) ≤ (x + 2 * ε) ^ 2 * m ∧
      (y - 2 * ε) ^ 2 * m ≤ ((T z).card : ENNReal) ∧
      ((T z).card : ENNReal) ≤ (y + 2 * ε) ^ 2 * m := by
    have hz := Finset.mem_sdiff.mp z.property
    have hF : ¬ (((S z).card : ENNReal) < (x - 2 * ε) ^ 2 * m ∨
        (x + 2 * ε) ^ 2 * m < ((S z).card : ENNReal)) := by
      intro h
      exact hz.2 (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz.1, h⟩)))
    have hH : ¬ (((T z).card : ENNReal) < (y - 2 * ε) ^ 2 * m ∨
        (y + 2 * ε) ^ 2 * m < ((T z).card : ENNReal)) := by
      intro h
      exact hz.2 (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz.1, h⟩)))
    exact ⟨le_of_not_gt (not_or.mp hF).1, le_of_not_gt (not_or.mp hF).2,
      le_of_not_gt (not_or.mp hH).1, le_of_not_gt (not_or.mp hH).2⟩
  let E (z : P) : Set {f : U → W // PerfectMatching G U W hUW f} := {f |
    ((S z).card : ENNReal) * (T z).card / m - ζ * m ≤
      ((Finset.univ.filter fun u : U => u.1 ∈ S z ∧ (f.1 u).1 ∈ T z).card : ENNReal) ∧
    ((Finset.univ.filter fun u : U => u.1 ∈ S z ∧ (f.1 u).1 ∈ T z).card : ENNReal) ≤
      ((S z).card : ENNReal) * (T z).card / m + ζ * m}
  have hE (z : P) : 1 - c ^ m ≤ μ.toOuterMeasure (E z) :=
    hconc (S z) (T z) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      ((mul_le_mul_right' hS _).trans (hbounds z).1)
      ((mul_le_mul_right' hT _).trans (hbounds z).2.2.1)
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
  have hfail (z : P) : μ.toOuterMeasure (E z)ᶜ ≤ c ^ m := by
    have hle : μ.toOuterMeasure (E z) ≤ 1 := by
      rw [← htotal (E z)]
      exact le_self_add
    apply ENNReal.le_of_add_le_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
    rw [htotal (E z)]
    exact tsub_le_iff_right.mp (hE z)
  have hfailAll : μ.toOuterMeasure (⋂ z : P, E z)ᶜ ≤ (Z.card : ENNReal) ^ 2 * c ^ m := by
    rw [Set.compl_iInter]
    calc
      _ ≤ ∑ z : P, μ.toOuterMeasure (E z)ᶜ := MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ _z : P, c ^ m := Finset.sum_le_sum (fun z _ => hfail z)
      _ = (P.card : ENNReal) * c ^ m := by simp [nsmul_eq_mul]
      _ ≤ _ := by
        have hc : P.card ≤ Z.card * Z.card := by
          simpa only [Finset.card_product] using Finset.card_le_card (Finset.sdiff_subset (s := Z ×ˢ Z) (t := BF ∪ BH))
        have hcE : (P.card : ENNReal) ≤ (Z.card : ENNReal) ^ 2 := by
          simpa only [Nat.cast_mul, pow_two] using (Nat.cast_le (α := ENNReal)).mpr hc
        exact mul_le_mul_right' hcE _
  have hsuccess : 1 - (Z.card : ENNReal) ^ 2 * c ^ m ≤ μ.toOuterMeasure (⋂ z : P, E z) := by
    apply tsub_le_iff_right.mpr
    rw [← htotal (⋂ z : P, E z)]
    exact add_le_add le_rfl hfailAll
  refine hsuccess.trans (MeasureTheory.measure_mono ?_)
  intro f hf
  let A := MatchingInducedGraph F H U W Z f.1
  letI : DecidableRel A.Adj := Classical.decRel _
  let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
  let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
  let B := (R ×ˢ R).filter fun z => (x * y + δ) ^ 2 * m <
    ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)
  let val : U ⊕ Z → V := Sum.elim Subtype.val Subtype.val
  have hmap : Set.MapsTo (fun z : (U ⊕ Z) × (U ⊕ Z) => (val z.1, val z.2))
      (↑B) (↑(BF ∪ BH : Finset (V × V))) := by
    intro z hz
    obtain ⟨hzR, hlarge⟩ := Finset.mem_filter.mp hz
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.mem_product.mp hzR).1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finset.mem_product.mp hzR).2
    change (val z.1, val z.2) ∈ BF ∪ BH
    rw [← ha, ← hb]
    change (a.1, b.1) ∈ BF ∪ BH
    by_contra hnot
    let p : P := ⟨(a.1, b.1), Finset.mem_sdiff.mpr
      ⟨Finset.mem_product.mpr ⟨a.property, b.property⟩, hnot⟩⟩
    have hp := (Set.mem_iInter.mp hf p).2
    obtain ⟨_, _, _, _, _, _, hcodeg⟩ := MatchingInducedGraphIdentities F H U W Z f.1
    rw [← ha, ← hb, hcodeg a b] at hlarge
    have hcard :
        (Finset.univ.filter fun u : U =>
          (F.Adj u a ∧ F.Adj u b) ∧ (H.Adj (f.1 u) a ∧ H.Adj (f.1 u) b)).card =
        (Finset.univ.filter fun u : U => u.1 ∈ S p ∧ (f.1 u).1 ∈ T p).card := by
      congr 1
      ext u
      simp [S, T, p]
    rw [hcard] at hlarge
    have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
    have hcenter : ((S p).card : ENNReal) * (T p).card / m ≤
        ((x + 2 * ε) ^ 2 * (y + 2 * ε) ^ 2) * m := by
      calc
        _ ≤ (((x + 2 * ε) ^ 2 * m) * ((y + 2 * ε) ^ 2 * m)) / m :=
          ENNReal.div_le_div_right (mul_le_mul' (hbounds p).2.1 (hbounds p).2.2.2) _
        _ = (((x + 2 * ε) ^ 2 * (y + 2 * ε) ^ 2) * m) * m / m := by congr 1; ac_rfl
        _ = _ := ENNReal.mul_div_cancel_right hm0 (by simp)
    apply (not_lt_of_ge (hp.trans ?_)) hlarge
    calc
      _ ≤ ((x + 2 * ε) ^ 2 * (y + 2 * ε) ^ 2) * m + ζ * m := add_le_add hcenter le_rfl
      _ = ((x + 2 * ε) ^ 2 * (y + 2 * ε) ^ 2 + ζ) * m := (add_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_right' hwindow _
  have hinjR : Set.InjOn val R := by
    intro u hu v hv huv
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
    exact congrArg Sum.inr (Subtype.ext huv)
  have hcard : B.card ≤ (BF ∪ BH).card := by
    apply Finset.card_le_card_of_injOn _ hmap
    intro z hz z' hz' h
    have hzR := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    have hzR' := Finset.mem_product.mp (Finset.mem_filter.mp hz').1
    exact Prod.ext (hinjR hzR.1 hzR'.1 (congrArg Prod.fst h))
      (hinjR hzR.2 hzR'.2 (congrArg Prod.snd h))
  change (B.card : ENNReal) ≤ 6 * ε * (Z.card : ENNReal) ^ 2
  calc
    _ ≤ ((BF ∪ BH).card : ENNReal) := by exact_mod_cast hcard
    _ ≤ (BF.card : ENNReal) + BH.card := by exact_mod_cast Finset.card_union_le BF BH
    _ ≤ 3 * ε * (Z.card : ENNReal) ^ 2 + 3 * ε * (Z.card : ENNReal) ^ 2 :=
      add_le_add hbadF hbadH
    _ = _ := by ring
