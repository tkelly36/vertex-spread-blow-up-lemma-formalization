import Tablet.IndependentRetentionConcentration
import Tablet.IndependentEdgeSample
import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.RetentionCountControl

open scoped NNReal
open MeasureTheory

-- [TABLET NODE: RetentionBadEventUnion]
theorem RetentionBadEventUnion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V)
    (q : ℝ≥0) (hq : q ≤ 1) (ξ : ℝ) (hξ : 0 < ξ)
    (η : ENNReal) (hη : 0 < η) (hηtop : η ≠ ⊤)
    (hL : 0 < L.card) (hR : 0 < R.card) :
    IndependentEdgeSample (V × V) q hq
      {ω | ¬ RetentionCountControl G L R q ξ η ω} ≤
      ENNReal.ofReal
        (2 * (L.card + R.card : ℝ) * Real.exp (-2 * ξ ^ 2 * min (L.card : ℝ) R.card) +
         2 * (2 : ℝ) ^ (L.card + R.card) *
           Real.exp (-2 * ξ ^ 2 * η.toReal ^ 2 * L.card * R.card)) := by
-- BODY
  classical
  let μ := IndependentEdgeSample (V × V) q hq
  have hlaw := IndependentUnequalEdgeSampleLaw (fun _ : V × V => q) (fun _ => hq)
  have hprob : IsProbabilityMeasure (IndependentEdgeSample (V × V) q hq) := by
    simpa only [IndependentEdgeSample] using hlaw.1
  letI : IsProbabilityMeasure μ := hprob
  let E := fun (I : Finset (V × V)) (m : ℕ) =>
    {ω | ξ * m < |(IndependentRetentionCount I ω : ℝ) - (q : ℝ) * I.card|}
  let IL := fun v => (({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2
  let IR := fun w => (L.product {w}).filter fun p => G.Adj p.1 p.2
  let IJ := fun p : Finset V × Finset V =>
    (p.1.product p.2).filter fun e => G.Adj e.1 e.2
  let J := (L.powerset.product R.powerset).filter fun p =>
    η * (L.card : ENNReal) < p.1.card ∧ η * (R.card : ENNReal) < p.2.card
  let EL := fun v => E (IL v) R.card
  let ER := fun w => E (IR w) L.card
  let EJ := fun p : Finset V × Finset V => E (IJ p) (p.1.card * p.2.card)
  let c := 2 * Real.exp (-2 * ξ ^ 2 * min (L.card : ℝ) R.card)
  let d := 2 * Real.exp (-2 * ξ ^ 2 * η.toReal ^ 2 * L.card * R.card)
  have htail (I : Finset (V × V)) (m : ℕ) (hm : 0 < m) (hI : I.card ≤ m)
      (t : ℝ) (ht : t ≤ m) : μ.real (E I m) ≤ 2 * Real.exp (-2 * ξ ^ 2 * t) := by
    have hb := IndependentRetentionConcentration q hq I m hm hI ξ hξ
    have hr : μ.real (E I m) ≤ 2 * Real.exp (-2 * ξ ^ 2 * m) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hb
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (by nlinarith [sq_nonneg ξ])))
      (by norm_num))
  have hleft (v : V) : μ.real (EL v) ≤ c := by
    apply htail (IL v) R.card hR _ _ (min_le_right _ _)
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hright (w : V) : μ.real (ER w) ≤ c := by
    apply htail (IR w) L.card hL _ _ (min_le_left _ _)
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hηreal : 0 < η.toReal := ENNReal.toReal_pos_iff.mpr ⟨hη, hηtop.lt_top⟩
  have hrect (p : Finset V × Finset V) (hp : p ∈ J) : μ.real (EJ p) ≤ d := by
    obtain ⟨_, hU, hW⟩ := Finset.mem_filter.mp hp
    have hUr : η.toReal * (L.card : ℝ) < p.1.card := by
      have hh := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hU
      simpa using hh
    have hWr : η.toReal * (R.card : ℝ) < p.2.card := by
      have hh := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hW
      simpa using hh
    have hapos : (0 : ℝ) < L.card := by exact_mod_cast hL
    have hbpos : (0 : ℝ) < R.card := by exact_mod_cast hR
    have hUp : (0 : ℝ) < p.1.card := (mul_pos hηreal hapos).trans hUr
    have hWp : (0 : ℝ) < p.2.card := (mul_pos hηreal hbpos).trans hWr
    have hm : 0 < p.1.card * p.2.card := by
      exact Nat.mul_pos (by exact_mod_cast hUp) (by exact_mod_cast hWp)
    have hprod : η.toReal ^ 2 * (L.card : ℝ) * R.card <
        (p.1.card : ℝ) * p.2.card := by
      calc
        _ = (η.toReal * L.card) * (η.toReal * R.card) := by ring
        _ < (p.1.card : ℝ) * p.2.card :=
          mul_lt_mul hUr hWr.le (mul_pos hηreal hbpos) hUp.le
    have hi : (IJ p).card ≤ p.1.card * p.2.card :=
      (Finset.card_filter_le _ _).trans (by simp [Finset.card_product])
    have ht : η.toReal ^ 2 * (L.card : ℝ) * R.card ≤ (p.1.card * p.2.card : ℕ) := by
      simpa only [Nat.cast_mul] using hprod.le
    have hh := htail (IJ p) (p.1.card * p.2.card) hm hi _ ht
    convert hh using 1 <;> dsimp [EJ, d] <;> congr 2 <;> ring
  have hJcard : (J.card : ℝ) ≤ (2 : ℝ) ^ (L.card + R.card) := by
    have hn : J.card ≤ 2 ^ (L.card + R.card) := by
      calc
        J.card ≤ (L.powerset.product R.powerset).card := Finset.card_filter_le _ _
        _ = 2 ^ (L.card + R.card) := by simp [Finset.card_product, pow_add]
    exact_mod_cast hn
  have hfinite {α : Type _} (s : Finset α) (f : α → Set (V × V → Bool))
      (b : ℝ) (hf : ∀ i ∈ s, μ.real (f i) ≤ b) :
      μ.real (⋃ i ∈ s, f i) ≤ s.card * b := by
    calc
      _ ≤ ∑ i ∈ s, μ.real (f i) := measureReal_biUnion_finset_le s f
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum hf
      _ = s.card * b := by simp [nsmul_eq_mul]
  have hsub : {ω | ¬ RetentionCountControl G L R q ξ η ω} ⊆
      ((⋃ v ∈ L, EL v) ∪ (⋃ w ∈ R, ER w)) ∪ (⋃ p ∈ J, EJ p) := by
    intro ω hω
    by_contra hn
    apply hω
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      apply le_of_not_gt
      intro h
      apply hn
      exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, h⟩⟩))
    · intro w hw
      apply le_of_not_gt
      intro h
      apply hn
      exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, h⟩⟩))
    · intro U hUL W hWR hU hW
      apply le_of_not_gt
      intro h
      apply hn
      have hp : (U, W) ∈ J := by
        simp only [J, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_powerset]
        exact ⟨⟨hUL, hWR⟩, hU, hW⟩
      have he : ω ∈ EJ (U, W) := by simpa only [EJ, E, Set.mem_setOf_eq, Nat.cast_mul] using h
      exact Or.inr (Set.mem_iUnion.mpr ⟨(U, W), Set.mem_iUnion.mpr ⟨hp, he⟩⟩)
  have hbound : μ.real {ω | ¬ RetentionCountControl G L R q ξ η ω} ≤
      (L.card : ℝ) * c + R.card * c + (2 : ℝ) ^ (L.card + R.card) * d := by
    calc
      _ ≤ μ.real (((⋃ v ∈ L, EL v) ∪ (⋃ w ∈ R, ER w)) ∪ (⋃ p ∈ J, EJ p)) :=
        measureReal_mono hsub
      _ ≤ (μ.real (⋃ v ∈ L, EL v) + μ.real (⋃ w ∈ R, ER w)) +
          μ.real (⋃ p ∈ J, EJ p) :=
        (measureReal_union_le _ _).trans
          (add_le_add (measureReal_union_le _ _) le_rfl)
      _ ≤ (L.card : ℝ) * c + R.card * c + J.card * d :=
        add_le_add (add_le_add (hfinite L EL c (fun v _ => hleft v))
          (hfinite R ER c (fun w _ => hright w))) (hfinite J EJ d hrect)
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hJcard (show 0 ≤ d by positivity))
  change μ _ ≤ _
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  convert hbound using 1 <;> dsimp [c, d] <;> ring
