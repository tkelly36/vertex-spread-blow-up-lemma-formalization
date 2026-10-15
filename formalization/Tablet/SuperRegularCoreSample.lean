import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.FiniteIndependentSubgaussianTail
import Mathlib.Combinatorics.SimpleGraph.Density

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: SuperRegularCoreSample]
theorem SuperRegularCoreSample
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U₀ W₀ : Finset V)
    (n : ℕ) (d h : ℝ) (hn : 0 < n) (hd : 0 < d) (hd1 : d < 1) (hh : 0 < h)
    (hUW : Disjoint U₀ W₀) (hU : U₀.card ≤ n) (hW : W₀.card ≤ n)
    (hdegU : ∀ u ∈ U₀, (d - 3 * h) * n ≤
      ((W₀.filter fun w => H.Adj u w).card : ℝ) ∧
      ((W₀.filter fun w => H.Adj u w).card : ℝ) ≤ (d + h) * n)
    (hdegW : ∀ w ∈ W₀, (d - 3 * h) * n ≤
      ((U₀.filter fun u => H.Adj u w).card : ℝ) ∧
      ((U₀.filter fun u => H.Adj u w).card : ℝ) ≤ (d + h) * n)
    (hrect : ∀ A ⊆ U₀, ∀ B ⊆ W₀, h * n < (A.card : ℝ) →
      h * n < (B.card : ℝ) → |(H.edgeDensity A B : ℝ) - d| < h / 2)
    (hdegreeCut : 4 * n * Real.exp (-2 * h ^ 2 * (n : ℝ)) < 1 / 4)
    (hrectangleCut : 2 * (4 : ℝ) ^ n *
      Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) < 1 / 4) :
    ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
      F ≤ H ∧
      (∀ ⦃u v⦄, F.Adj u v →
        (u ∈ U₀ ∧ v ∈ W₀) ∨ (u ∈ W₀ ∧ v ∈ U₀)) ∧
      (∀ u ∈ U₀, (d ^ 2 / 2 - 4 * h) * n ≤
        ((W₀.filter fun w => F.Adj u w).card : ℝ) ∧
        ((W₀.filter fun w => F.Adj u w).card : ℝ) ≤ (d ^ 2 / 2 + 2 * h) * n) ∧
      (∀ w ∈ W₀, (d ^ 2 / 2 - 4 * h) * n ≤
        ((U₀.filter fun u => F.Adj u w).card : ℝ) ∧
        ((U₀.filter fun u => F.Adj u w).card : ℝ) ≤ (d ^ 2 / 2 + 2 * h) * n) ∧
      (∀ A ⊆ U₀, ∀ B ⊆ W₀, h * n < (A.card : ℝ) →
        h * n < (B.card : ℝ) → |(F.edgeDensity A B : ℝ) - d ^ 2 / 2| ≤ 2 * h) := by
-- BODY
  classical
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let p : ℝ := d / 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; linarith only [hd1]
  have hpd : p * d = d ^ 2 / 2 := by dsimp [p]; ring
  let E0 := (U₀.product W₀).filter fun e => H.Adj e.1 e.2
  let I := {e // e ∈ E0}
  let q : I → ℝ≥0 := fun _ => ⟨p, hp.le⟩
  have hq : ∀ e, q e ≤ 1 := fun _ => by exact_mod_cast hp1
  let μ := Measure.pi (fun e => (PMF.bernoulli (q e) (hq e)).toMeasure)
  obtain ⟨hμ, hi, _, hs⟩ := IndependentUnequalEdgeSampleLaw q hq
  change IsProbabilityMeasure μ at hμ
  letI := hμ
  let X : I → (I → Bool) → ℝ := fun e ω => if ω e then 1 else 0
  let Y : I → (I → Bool) → ℝ := fun e ω => X e ω - p
  have hind : iIndepFun Y μ :=
    hi.comp (fun _ x => x - p) (fun _ => measurable_id.sub_const _)
  have hsg : ∀ e, HasSubgaussianMGF (Y e) (1 / 4) μ := hs
  let F : (I → Bool) → SimpleGraph V := fun ω =>
    { Adj := fun u w => H.Adj u w ∧
        ((∃ he : (u, w) ∈ E0, ω ⟨(u, w), he⟩ = true) ∨
         (∃ he : (w, u) ∈ E0, ω ⟨(w, u), he⟩ = true))
      symm := by
        intro u w huv
        exact ⟨huv.1.symm, huv.2.symm⟩
      loopless := ⟨fun u huu => H.loopless.irrefl u huu.1⟩ }
  have hcontain (ω) : F ω ≤ H := fun _ _ huv => huv.1
  have hcross (ω : I → Bool) (u) (hu : u ∈ U₀) (w) (hw : w ∈ W₀) :
      (F ω).Adj u w ↔ ∃ he : (u, w) ∈ E0, ω ⟨(u, w), he⟩ = true := by
    constructor
    · rintro ⟨_, h | h⟩
      · exact h
      · obtain ⟨hwu, _⟩ := h
        have hwU := (Finset.mem_product.mp (Finset.mem_filter.mp hwu).1).1
        exact False.elim (Finset.disjoint_left.mp hUW hwU hw)
    · rintro ⟨huw, hω⟩
      exact ⟨(Finset.mem_filter.mp huw).2, Or.inl ⟨huw, hω⟩⟩
  let s : Finset V → Finset V → Finset I := fun A B =>
    Finset.univ.filter fun e => e.val ∈ A.product B
  have hsum (A B : Finset V) (hAU : A ⊆ U₀) (hBW : B ⊆ W₀)
      (f : V × V → ℝ) :
      ∑ e ∈ s A B, f e.val =
        ∑ e ∈ (A.product B).filter (fun e => H.Adj e.1 e.2), f e := by
    apply Finset.sum_bij (fun e _ => e.val)
    · intro e hem
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hem).2, (Finset.mem_filter.mp e.property).2⟩
    · intro e he f hf hef
      exact Subtype.ext hef
    · intro e hem
      obtain ⟨heAB, heG⟩ := Finset.mem_filter.mp hem
      obtain ⟨heA, heB⟩ := Finset.mem_product.mp heAB
      have heE : e ∈ E0 := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hAU heA, hBW heB⟩, heG⟩
      exact ⟨⟨e, heE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heAB⟩, rfl⟩
    · intro e hem
      rfl
  have hcount (A B : Finset V) (hAU : A ⊆ U₀) (hBW : B ⊆ W₀) (ω : I → Bool) :
      (((A.product B).filter fun e => (F ω).Adj e.1 e.2).card : ℝ) =
        ∑ e ∈ s A B, X e ω := by
    let f : V × V → ℝ := fun e => if he : e ∈ E0 then X ⟨e, he⟩ ω else 0
    have hsf : ∑ e ∈ s A B, X e ω = ∑ e ∈ s A B, f e.val := by
      apply Finset.sum_congr rfl
      intro e hem
      simp only [f, dif_pos e.property]
      rfl
    rw [hsf, hsum A B hAU hBW f]
    have hfull : ∑ e ∈ (A.product B).filter (fun e => H.Adj e.1 e.2), f e =
        ∑ e ∈ A.product B, f e := by
      apply Finset.sum_filter_of_ne
      intro e hem hf
      by_contra hg
      have hnE : e ∉ E0 := fun heE => hg (Finset.mem_filter.mp heE).2
      exact hf (dif_neg hnE)
    rw [hfull, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e hem
    obtain ⟨heA, heB⟩ := Finset.mem_product.mp hem
    have hcross' := hcross ω e.1 (hAU heA) e.2 (hBW heB)
    by_cases heE : e ∈ E0
    · simp only [f, dif_pos heE, X]
      have hcross'' : (F ω).Adj e.1 e.2 ↔ ω ⟨e, heE⟩ = true := by
        refine ⟨fun hadj => ?_, fun hω => hcross'.mpr ⟨heE, hω⟩⟩
        obtain ⟨heE', hω⟩ := hcross'.mp hadj
        exact hω
      simp only [hcross'']
    · have hnot : ¬(F ω).Adj e.1 e.2 := fun hadj =>
        (hcross'.mp hadj).elim (fun he _ => heE he)
      simp only [hnot, if_false, f, dif_neg heE]
  have hmean (A B : Finset V) (hAU : A ⊆ U₀) (hBW : B ⊆ W₀) :
      ∑ _e ∈ s A B, p =
        p * (((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ) := by
    rw [hsum A B hAU hBW (fun _ => p)]
    simp [mul_comm]
  have htrials (A B : Finset V) : (s A B).card ≤ A.card * B.card := by
    have hinj : Function.Injective (fun e : I => e.val) := Subtype.val_injective
    have hsub : (s A B).image (fun e => e.val) ⊆ A.product B := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hi).2
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hinj, Finset.product_eq_sprod,
      Finset.card_product] at this
  have hrowcard (F : SimpleGraph V) [DecidableRel F.Adj] (u : V) :
      ((({u} : Finset V).product W₀).filter fun e => F.Adj e.1 e.2).card =
        (W₀.filter fun w => F.Adj u w).card := by
    have he : ((({u} : Finset V).product W₀).filter fun e => F.Adj e.1 e.2) =
        ({u} : Finset V).product (W₀.filter fun w => F.Adj u w) := by
      ext e
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨rfl, hw⟩, ha⟩
        exact ⟨rfl, hw, ha⟩
      · rintro ⟨rfl, hw, ha⟩
        exact ⟨⟨rfl, hw⟩, ha⟩
    rw [he, Finset.product_eq_sprod, Finset.card_product]
    simp
  have hcolcard (F : SimpleGraph V) [DecidableRel F.Adj] (w : V) :
      ((U₀.product ({w} : Finset V)).filter fun e => F.Adj e.1 e.2).card =
        (U₀.filter fun u => F.Adj u w).card := by
    have he : ((U₀.product ({w} : Finset V)).filter fun e => F.Adj e.1 e.2) =
        (U₀.filter fun u => F.Adj u w).product ({w} : Finset V) := by
      ext e
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hu, he⟩, ha⟩
        rw [he] at ha
        exact ⟨⟨hu, ha⟩, he⟩
      · rintro ⟨⟨hu, ha⟩, he⟩
        rw [← he] at ha
        exact ⟨⟨hu, he⟩, ha⟩
    rw [he, Finset.product_eq_sprod, Finset.card_product]
    simp
  let badU : V → Set (I → Bool) := fun u =>
    {ω | h * n < |∑ e ∈ s {u} W₀, Y e ω|}
  let badW : V → Set (I → Bool) := fun w =>
    {ω | h * n < |∑ e ∈ s U₀ {w}, Y e ω|}
  have hdegreeTail (A B : Finset V) (hr : (s A B).card ≤ n) :
      μ.real {ω | h * n < |∑ e ∈ s A B, Y e ω|} ≤
        2 * Real.exp (-2 * h ^ 2 * (n : ℝ)) := by
    have ht : 0 ≤ h * (n : ℝ) := by positivity
    have hb := FiniteIndependentSubgaussianTail μ Y (s A B) hind
      (fun e _ => hsg e) n (h * n) hnr (Nat.cast_le.mpr hr) ht
    have heq : -2 * (h * (n : ℝ)) ^ 2 / n = -2 * h ^ 2 * (n : ℝ) := by
      field_simp
    rwa [heq] at hb
  have htailU (u) : μ.real (badU u) ≤ 2 * Real.exp (-2 * h ^ 2 * (n : ℝ)) := by
    apply hdegreeTail
    simpa only [Finset.card_singleton, one_mul] using
      (htrials {u} W₀).trans (by simpa using hW)
  have htailW (w) : μ.real (badW w) ≤ 2 * Real.exp (-2 * h ^ 2 * (n : ℝ)) := by
    apply hdegreeTail
    simpa only [Finset.card_singleton, mul_one] using
      (htrials U₀ {w}).trans (by simpa using hU)
  let bad : Finset V × Finset V → Set (I → Bool) := fun AB =>
    {ω | h * n < (AB.1.card : ℝ) ∧ h * n < (AB.2.card : ℝ) ∧
      h * AB.1.card * AB.2.card < |∑ e ∈ s AB.1 AB.2, Y e ω|}
  have htail (AB : Finset V × Finset V) :
      μ.real (bad AB) ≤ 2 * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) := by
    by_cases hA : h * n < (AB.1.card : ℝ)
    · by_cases hB : h * n < (AB.2.card : ℝ)
      · let N : ℝ := (AB.1.card : ℝ) * AB.2.card
        have hhn : 0 < h * (n : ℝ) := mul_pos hh hnr
        have hapos : 0 < (AB.1.card : ℝ) := hhn.trans hA
        have hbpos : 0 < (AB.2.card : ℝ) := hhn.trans hB
        have hN : 0 < N := mul_pos hapos hbpos
        have hr : ((s AB.1 AB.2).card : ℝ) ≤ N := by
          dsimp only [N]
          exact_mod_cast htrials AB.1 AB.2
        have ht : 0 ≤ h * N := by positivity
        have hbound := FiniteIndependentSubgaussianTail μ Y (s AB.1 AB.2) hind
          (fun e _ => hsg e) N (h * N) hN hr ht
        have hsub : bad AB ⊆ {ω | h * N < |∑ e ∈ s AB.1 AB.2, Y e ω|} := by
          intro ω hω
          change h * N < |∑ e ∈ s AB.1 AB.2, Y e ω|
          simpa only [N, mul_assoc] using hω.2.2
        have heq : -2 * (h * N) ^ 2 / N = -2 * h ^ 2 * N := by
          field_simp
        have hNlo : h ^ 2 * (n : ℝ) ^ 2 ≤ N := by
          calc
            h ^ 2 * (n : ℝ) ^ 2 = (h * n) * (h * n) := by ring
            _ ≤ (AB.1.card : ℝ) * AB.2.card :=
              mul_le_mul hA.le hB.le hhn.le hapos.le
        have hexp : -2 * h ^ 2 * N ≤ -2 * h ^ 4 * (n : ℝ) ^ 2 := by
          nlinarith only [mul_le_mul_of_nonneg_left hNlo (sq_nonneg h)]
        rw [heq] at hbound
        exact (measureReal_mono hsub).trans
          (hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)))
      · have hempty : bad AB = ∅ := by
          ext ω
          simp only [bad, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hω => hB hω.2.1
        rw [hempty, measureReal_empty]
        positivity
    · have hempty : bad AB = ∅ := by
        ext ω
        simp only [bad, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hω => hA hω.1
      rw [hempty, measureReal_empty]
      positivity
  let tests := U₀.powerset.product W₀.powerset
  have htests : (tests.card : ℝ) ≤ (4 : ℝ) ^ n := by
    have hu : (2 : ℝ) ^ U₀.card ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num) hU
    have hw : (2 : ℝ) ^ W₀.card ≤ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num) hW
    change ((U₀.powerset.product W₀.powerset).card : ℝ) ≤ (4 : ℝ) ^ n
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_powerset,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (2 : ℝ) ^ n * 2 ^ n := mul_le_mul hu hw (by positivity) (by positivity)
      _ = (4 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  let degreeFailure := (⋃ u ∈ U₀, badU u) ∪ (⋃ w ∈ W₀, badW w)
  let rectangleFailure := ⋃ AB ∈ tests, bad AB
  have hfinite {β : Type _} (t : Finset β) (f : β → Set (I → Bool))
      (b : ℝ) (hf : ∀ i ∈ t, μ.real (f i) ≤ b) :
      μ.real (⋃ i ∈ t, f i) ≤ t.card * b := by
    calc
      _ ≤ ∑ i ∈ t, μ.real (f i) := measureReal_biUnion_finset_le t f
      _ ≤ ∑ _i ∈ t, b := Finset.sum_le_sum hf
      _ = t.card * b := by simp [nsmul_eq_mul]
  have hdfail : μ.real degreeFailure < 1 / 4 := by
    have hb : 0 ≤ 2 * Real.exp (-2 * h ^ 2 * (n : ℝ)) := by positivity
    calc
      _ ≤ μ.real (⋃ u ∈ U₀, badU u) + μ.real (⋃ w ∈ W₀, badW w) :=
        measureReal_union_le _ _
      _ ≤ (U₀.card : ℝ) * (2 * Real.exp (-2 * h ^ 2 * (n : ℝ))) +
          W₀.card * (2 * Real.exp (-2 * h ^ 2 * (n : ℝ))) :=
        add_le_add (hfinite U₀ badU _ (fun u _ => htailU u))
          (hfinite W₀ badW _ (fun w _ => htailW w))
      _ ≤ (n : ℝ) * (2 * Real.exp (-2 * h ^ 2 * (n : ℝ))) +
          n * (2 * Real.exp (-2 * h ^ 2 * (n : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hU) hb)
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hW) hb)
      _ = 4 * n * Real.exp (-2 * h ^ 2 * (n : ℝ)) := by ring
      _ < 1 / 4 := hdegreeCut
  have hrfail : μ.real rectangleFailure < 1 / 4 := by
    calc
      _ ≤ (tests.card : ℝ) * (2 * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2)) :=
        hfinite tests bad _ (fun AB _ => htail AB)
      _ ≤ (4 : ℝ) ^ n * (2 * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right htests (by positivity)
      _ = 2 * (4 : ℝ) ^ n * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) := by ring
      _ < 1 / 4 := hrectangleCut
  let failure := degreeFailure ∪ rectangleFailure
  -- Select only after bounding both families under the same product law.
  have hfail : μ.real failure < 1 := by
    have hb : μ.real failure ≤ μ.real degreeFailure + μ.real rectangleFailure :=
      measureReal_union_le _ _
    linarith only [hb, hdfail, hrfail]
  obtain ⟨ω, hgood⟩ : ∃ ω, ω ∉ failure := by
    have hm : MeasurableSet failure := (Set.to_countable failure).measurableSet
    have hpos : μ failureᶜ ≠ 0 := by
      apply (measureReal_eq_zero_iff).not.mp
      rw [probReal_compl_eq_one_sub hm]
      linarith only [hfail]
    exact nonempty_of_measure_ne_zero hpos
  have hgoodU (u) (hu : u ∈ U₀) : |∑ e ∈ s {u} W₀, Y e ω| ≤ h * n := by
    apply le_of_not_gt
    intro hb
    apply hgood
    exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hb⟩⟩))
  have hgoodW (w) (hw : w ∈ W₀) : |∑ e ∈ s U₀ {w}, Y e ω| ≤ h * n := by
    apply le_of_not_gt
    intro hb
    apply hgood
    exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hb⟩⟩))
  have hsupport (ω : I → Bool) : ∀ ⦃u v⦄, (F ω).Adj u v →
      (u ∈ U₀ ∧ v ∈ W₀) ∨ (u ∈ W₀ ∧ v ∈ U₀) := by
    rintro u v ⟨_, huv | hvu⟩
    · obtain ⟨he, _⟩ := huv
      exact Or.inl (Finset.mem_product.mp (Finset.mem_filter.mp he).1)
    · obtain ⟨he, _⟩ := hvu
      exact Or.inr (Finset.mem_product.mp (Finset.mem_filter.mp he).1).symm
  have hdegree (a b : ℝ)
      (hlo : (d - 3 * h) * n ≤ a) (hhi : a ≤ (d + h) * n)
      (hb : |b - p * a| ≤ h * n) :
      (d ^ 2 / 2 - 4 * h) * n ≤ b ∧ b ≤ (d ^ 2 / 2 + 2 * h) * n := by
    have hl := mul_le_mul_of_nonneg_left hlo hp.le
    have hu := mul_le_mul_of_nonneg_left hhi hp.le
    have hph := mul_le_mul_of_nonneg_right hp1 (mul_pos hh hnr).le
    have hprod : p * d * n = d ^ 2 / 2 * n := by rw [hpd]
    obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
    constructor <;> nlinarith only [hl, hu, hph, hprod, hblo, hbhi]
  refine ⟨F ω, inferInstance, hcontain ω, hsupport ω, ?_, ?_, ?_⟩
  · intro u hu
    have hcount' := hcount {u} W₀ (Finset.singleton_subset_iff.mpr hu)
      (Finset.Subset.refl _) ω
    have hmean' := hmean {u} W₀ (Finset.singleton_subset_iff.mpr hu)
      (Finset.Subset.refl _)
    rw [hrowcard (F ω) u] at hcount'
    rw [hrowcard H u] at hmean'
    have hb := hgoodU u hu
    simp only [Y, Finset.sum_sub_distrib] at hb
    rw [← hcount', hmean'] at hb
    exact hdegree _ _ (hdegU u hu).1 (hdegU u hu).2 hb
  · intro w hw
    have hcount' := hcount U₀ {w} (Finset.Subset.refl _)
      (Finset.singleton_subset_iff.mpr hw) ω
    have hmean' := hmean U₀ {w} (Finset.Subset.refl _)
      (Finset.singleton_subset_iff.mpr hw)
    rw [hcolcard (F ω) w] at hcount'
    rw [hcolcard H w] at hmean'
    have hb := hgoodW w hw
    simp only [Y, Finset.sum_sub_distrib] at hb
    rw [← hcount', hmean'] at hb
    exact hdegree _ _ (hdegW w hw).1 (hdegW w hw).2 hb
  · intro A hAU B hBW hA hB
    have hm : (A, B) ∈ tests := Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hAU, Finset.mem_powerset.mpr hBW⟩
    have hb : |∑ e ∈ s A B, Y e ω| ≤ h * A.card * B.card := by
      apply le_of_not_gt
      intro hb
      apply hgood
      exact Or.inr (Set.mem_iUnion.mpr ⟨(A, B), Set.mem_iUnion.mpr ⟨hm, hA, hB, hb⟩⟩)
    have hsample : |(((A.product B).filter fun e => (F ω).Adj e.1 e.2).card : ℝ) -
        p * (((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ)| ≤
          h * A.card * B.card := by
      rw [hcount A B hAU hBW ω, ← hmean A B hAU hBW]
      simpa only [Y, Finset.sum_sub_distrib] using hb
    have hAp : 0 < (A.card : ℝ) := (mul_pos hh hnr).trans hA
    have hBp : 0 < (B.card : ℝ) := (mul_pos hh hnr).trans hB
    have hden : 0 < (A.card : ℝ) * B.card := mul_pos hAp hBp
    have hdensity : |((F ω).edgeDensity A B : ℝ) -
        p * (H.edgeDensity A B : ℝ)| ≤ h := by
      have hid : ((F ω).edgeDensity A B : ℝ) - p * (H.edgeDensity A B : ℝ) =
          ((((A.product B).filter fun e => (F ω).Adj e.1 e.2).card : ℝ) -
            p * (((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ)) /
              ((A.card : ℝ) * B.card) := by
        simp only [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def,
          Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Finset.product_eq_sprod]
        ring
      rw [hid, abs_div, abs_of_pos hden]
      apply (div_le_iff₀ hden).mpr
      simpa only [mul_assoc] using hsample
    have hex := (hrect A hAU B hBW hA hB).le
    have hmeanDensity : |p * (H.edgeDensity A B : ℝ) - d ^ 2 / 2| ≤ h := by
      rw [← hpd, ← mul_sub, abs_mul, abs_of_pos hp]
      have he := mul_le_mul_of_nonneg_left hex hp.le
      have hph : p * (h / 2) ≤ h := by
        have he := mul_le_mul_of_nonneg_right hp1 (by positivity : 0 ≤ h / 2)
        linarith only [he, hh]
      exact he.trans hph
    exact (abs_sub_le ((F ω).edgeDensity A B : ℝ)
      (p * (H.edgeDensity A B : ℝ)) (d ^ 2 / 2)).trans
        (by linarith only [hdensity, hmeanDensity])
