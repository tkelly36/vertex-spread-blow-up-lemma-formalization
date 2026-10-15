import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Tablet.RegularExtractionPartitionGeometry
import Tablet.WeightedRectangleExpectation
import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.FiniteIndependentSubgaussianTail

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: SuperRegularInitialSample]
theorem SuperRegularInitialSample
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (n l M : ℕ) (ε d h γ α : ℝ)
    (hU : U.card = n) (hW : W.card = n) (hUW : Disjoint U W)
    (hcover : U ∪ W = Finset.univ)
    (hbip : ∀ ⦃u v⦄, G.Adj u v →
      (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U))
    (hl : 1 ≤ l) (hlM : l ≤ M) (hMn : M ≤ n)
    (hbound : SzemerediRegularity.bound α l ≤ M)
    (hε : 0 < ε) (hd : 0 < d) (hd1 : d < 1) (hh : 0 < h)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hα : 0 < α)
    (hαγ : α ≤ γ) (hαγγ : α ≤ γ ^ 2) (hεM : ε * M < γ)
    (hmargin : 2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2 < h / 4)
    (hdegreeCut : 4 * n * Real.exp (-(d ^ 2 / 2) ^ 2 * (n : ℝ) / 8) < 1 / 4)
    (hrectangleCut : 2 * (4 : ℝ) ^ n *
      Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1 / 4)
    (hlower : ∀ A ⊆ U, ∀ B ⊆ W, ε * n < (A.card : ℝ) →
      ε * n < (B.card : ℝ) → d ≤ (G.edgeDensity A B : ℝ))
    (hdegU : ∀ u ∈ U, d * n ≤ ((W.filter fun w => G.Adj u w).card : ℝ))
    (hdegW : ∀ w ∈ W, d * n ≤ ((U.filter fun u => G.Adj u w).card : ℝ)) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧
      (∀ u ∈ U, (7 * (d ^ 2 / 2) / 4) * n ≤
        ((W.filter fun w => H.Adj u w).card : ℝ)) ∧
      (∀ w ∈ W, (7 * (d ^ 2 / 2) / 4) * n ≤
        ((U.filter fun u => H.Adj u w).card : ℝ)) ∧
      (∀ A ⊆ U, ∀ B ⊆ W, h * n < (A.card : ℝ) →
        h * n < (B.card : ℝ) → |(H.edgeDensity A B : ℝ) - d| < h / 2) := by
-- BODY
  classical
  have hn : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have htotal : Fintype.card V = 2 * n := by
    simpa only [Finset.card_univ] using
      (hcover ▸ Finset.card_union_of_disjoint hUW).trans (by rw [hU, hW]; omega)
  obtain ⟨P, heq, hlP, hPb, hunif⟩ :=
    szemeredi_regularity G (l := l) hα (by omega)
  obtain ⟨_, E, hEP, _, hD, hslice, harea⟩ :=
    RegularExtractionPartitionGeometry G U W n l M ε d γ α hU hW hUW hcover
      hl hMn hε hd hγ hγ1 hα hαγ hαγγ hεM hlower P heq hlP
      (hPb.trans hbound) hunif
  obtain ⟨p, hp, hzero, _, hformula, _, happrox⟩ :=
    WeightedRectangleExpectation G U W n l d γ α hU hW hd hd1.le hγ hα
      P E hEP hD hslice harea
  have hpedge (u) (hu : u ∈ U) (w) (hw : w ∈ W) (huw : G.Adj u w) :
      d ≤ p (u, w) := by
    have hSu : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ _)
    have hTw : P.part w ∈ P.parts := P.part_mem.mpr (Finset.mem_univ _)
    have huS : u ∈ U ∩ P.part u :=
      Finset.mem_inter.mpr ⟨hu, P.mem_part (Finset.mem_univ _)⟩
    have hwT : w ∈ W ∩ P.part w :=
      Finset.mem_inter.mpr ⟨hw, P.mem_part (Finset.mem_univ _)⟩
    rw [hformula _ hSu _ hTw _ huS _ hwT huw]
    split_ifs with he
    · have hden := hD _ _ he
      have hpos := hd.trans_le hden.1
      apply (le_div_iff₀ hpos).mpr
      exact (mul_le_mul_of_nonneg_left hden.2 hd.le).trans_eq (mul_one d)
    · exact hd1.le
  have hexpect := happrox h hh hmargin
  let c : ℝ := d ^ 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  -- Each original edge has one coordinate, oriented from U to W.
  let E0 := (U.product W).filter fun e => G.Adj e.1 e.2
  let I := {e // e ∈ E0}
  let q : I → ℝ≥0 := fun e => ⟨p e.val, (hp e.val).1⟩
  have hq : ∀ e, q e ≤ 1 := fun e => by exact_mod_cast (hp e.val).2
  let μ := Measure.pi (fun e => (PMF.bernoulli (q e) (hq e)).toMeasure)
  obtain ⟨hμ, hi, _, hs⟩ := IndependentUnequalEdgeSampleLaw q hq
  change IsProbabilityMeasure μ at hμ
  letI := hμ
  let X : I → (I → Bool) → ℝ := fun e ω => if ω e then 1 else 0
  let Y : I → (I → Bool) → ℝ := fun e ω => X e ω - p e.val
  have hind : iIndepFun Y μ :=
    hi.comp (fun e x => x - p e.val) (fun _ => measurable_id.sub_const _)
  have hsg : ∀ e, HasSubgaussianMGF (Y e) (1 / 4) μ := hs
  let H : (I → Bool) → SimpleGraph V := fun ω =>
    { Adj := fun u w => G.Adj u w ∧
        ((∃ he : (u, w) ∈ E0, ω ⟨(u, w), he⟩ = true) ∨
         (∃ he : (w, u) ∈ E0, ω ⟨(w, u), he⟩ = true))
      symm := by
        intro u w huv
        exact ⟨huv.1.symm, huv.2.symm⟩
      loopless := ⟨fun u huu => G.loopless.irrefl u huu.1⟩ }
  have hcontain (ω) : H ω ≤ G := fun _ _ huv => huv.1
  have hcross (ω : I → Bool) (u) (hu : u ∈ U) (w) (hw : w ∈ W) :
      (H ω).Adj u w ↔ ∃ he : (u, w) ∈ E0, ω ⟨(u, w), he⟩ = true := by
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
  have hsum (A B : Finset V) (hAU : A ⊆ U) (hBW : B ⊆ W)
      (f : V × V → ℝ) :
      ∑ e ∈ s A B, f e.val =
        ∑ e ∈ (A.product B).filter (fun e => G.Adj e.1 e.2), f e := by
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
  have hcount (A B : Finset V) (hAU : A ⊆ U) (hBW : B ⊆ W) (ω : I → Bool) :
      (((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ) =
        ∑ e ∈ s A B, X e ω := by
    let f : V × V → ℝ := fun e => if he : e ∈ E0 then X ⟨e, he⟩ ω else 0
    have hsf : ∑ e ∈ s A B, X e ω = ∑ e ∈ s A B, f e.val := by
      apply Finset.sum_congr rfl
      intro e hem
      simp only [f, dif_pos e.property]
      rfl
    rw [hsf, hsum A B hAU hBW f]
    have hfull : ∑ e ∈ (A.product B).filter (fun e => G.Adj e.1 e.2), f e =
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
      have hcross'' : (H ω).Adj e.1 e.2 ↔ ω ⟨e, heE⟩ = true := by
        refine ⟨fun hadj => ?_, fun hω => hcross'.mpr ⟨heE, hω⟩⟩
        obtain ⟨heE', hω⟩ := hcross'.mp hadj
        exact hω
      simp only [hcross'']
    · have hnot : ¬(H ω).Adj e.1 e.2 := fun hadj =>
        (hcross'.mp hadj).elim (fun he _ => heE he)
      simp only [hnot, if_false, f, dif_neg heE]
  have hmean (A B : Finset V) (hAU : A ⊆ U) (hBW : B ⊆ W) :
      ∑ e ∈ s A B, p e.val = ∑ e ∈ A.product B, p e := by
    rw [hsum A B hAU hBW p]
    apply Finset.sum_filter_of_ne
    intro e hem hne
    by_contra hg
    exact hne (hzero e hg)
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
      ((({u} : Finset V).product W).filter fun e => F.Adj e.1 e.2).card =
        (W.filter fun w => F.Adj u w).card := by
    have he : ((({u} : Finset V).product W).filter fun e => F.Adj e.1 e.2) =
        ({u} : Finset V).product (W.filter fun w => F.Adj u w) := by
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
      ((U.product ({w} : Finset V)).filter fun e => F.Adj e.1 e.2).card =
        (U.filter fun u => F.Adj u w).card := by
    have he : ((U.product ({w} : Finset V)).filter fun e => F.Adj e.1 e.2) =
        (U.filter fun u => F.Adj u w).product ({w} : Finset V) := by
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
  have hmeanlo (A B : Finset V) (hAU : A ⊆ U) (hBW : B ⊆ W) :
      d * (((A.product B).filter fun e => G.Adj e.1 e.2).card : ℝ) ≤
        ∑ e ∈ s A B, p e.val := by
    rw [hsum A B hAU hBW p]
    calc
      _ = ∑ _e ∈ (A.product B).filter (fun e => G.Adj e.1 e.2), d := by
        simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨heAB, heG⟩ := Finset.mem_filter.mp he
        obtain ⟨heA, heB⟩ := Finset.mem_product.mp heAB
        exact hpedge e.1 (hAU heA) e.2 (hBW heB) heG
  have hrowmean (u) (hu : u ∈ U) : 2 * c * n ≤ ∑ e ∈ s {u} W, p e.val := by
    have hlo := hmeanlo {u} W (Finset.singleton_subset_iff.mpr hu) (Finset.Subset.refl _)
    rw [hrowcard] at hlo
    have hdeg := mul_le_mul_of_nonneg_left (hdegU u hu) hd.le
    dsimp only [c]
    nlinarith only [hlo, hdeg]
  have hcolmean (w) (hw : w ∈ W) : 2 * c * n ≤ ∑ e ∈ s U {w}, p e.val := by
    have hlo := hmeanlo U {w} (Finset.Subset.refl _) (Finset.singleton_subset_iff.mpr hw)
    rw [hcolcard] at hlo
    have hdeg := mul_le_mul_of_nonneg_left (hdegW w hw) hd.le
    dsimp only [c]
    nlinarith only [hlo, hdeg]
  let badU : V → Set (I → Bool) := fun u =>
    {ω | c * n / 4 < |∑ e ∈ s {u} W, Y e ω|}
  let badW : V → Set (I → Bool) := fun w =>
    {ω | c * n / 4 < |∑ e ∈ s U {w}, Y e ω|}
  have hdegreeTail (A B : Finset V) (hr : (s A B).card ≤ n) :
      μ.real {ω | c * n / 4 < |∑ e ∈ s A B, Y e ω|} ≤
        2 * Real.exp (-c ^ 2 * (n : ℝ) / 8) := by
    have ht : 0 ≤ c * (n : ℝ) / 4 := by positivity
    have hb := FiniteIndependentSubgaussianTail μ Y (s A B) hind
      (fun e _ => hsg e) n (c * n / 4) hnr (Nat.cast_le.mpr hr) ht
    have heq : -2 * (c * (n : ℝ) / 4) ^ 2 / n = -c ^ 2 * (n : ℝ) / 8 := by
      field_simp
      ring
    rwa [heq] at hb
  have htailU (u) : μ.real (badU u) ≤ 2 * Real.exp (-c ^ 2 * (n : ℝ) / 8) := by
    apply hdegreeTail
    simpa only [Finset.card_singleton, one_mul, hW] using htrials {u} W
  have htailW (w) : μ.real (badW w) ≤ 2 * Real.exp (-c ^ 2 * (n : ℝ) / 8) := by
    apply hdegreeTail
    simpa only [Finset.card_singleton, mul_one, hU] using htrials U {w}
  let bad : Finset V × Finset V → Set (I → Bool) := fun AB =>
    {ω | h * n < (AB.1.card : ℝ) ∧ h * n < (AB.2.card : ℝ) ∧
      (h / 4) * AB.1.card * AB.2.card < |∑ e ∈ s AB.1 AB.2, Y e ω|}
  have htail (AB : Finset V × Finset V) :
      μ.real (bad AB) ≤ 2 * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) := by
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
        have ht : 0 ≤ (h / 4) * N := by positivity
        have hbound := FiniteIndependentSubgaussianTail μ Y (s AB.1 AB.2) hind
          (fun e _ => hsg e) N ((h / 4) * N) hN hr ht
        have hsub : bad AB ⊆ {ω | (h / 4) * N < |∑ e ∈ s AB.1 AB.2, Y e ω|} := by
          intro ω hω
          change (h / 4) * N < |∑ e ∈ s AB.1 AB.2, Y e ω|
          simpa only [N, mul_assoc] using hω.2.2
        have heq : -2 * ((h / 4) * N) ^ 2 / N = -h ^ 2 * N / 8 := by
          field_simp
          ring
        have hNlo : h ^ 2 * (n : ℝ) ^ 2 ≤ N := by
          calc
            h ^ 2 * (n : ℝ) ^ 2 = (h * n) * (h * n) := by ring
            _ ≤ (AB.1.card : ℝ) * AB.2.card :=
              mul_le_mul hA.le hB.le hhn.le hapos.le
        have hexp : -h ^ 2 * N / 8 ≤ -h ^ 4 * (n : ℝ) ^ 2 / 8 := by
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
  let tests := U.powerset.product W.powerset
  have htests : (tests.card : ℝ) = (4 : ℝ) ^ n := by
    change ((U.powerset.product W.powerset).card : ℝ) = (4 : ℝ) ^ n
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_powerset, hU, hW,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  let degreeFailure := (⋃ u ∈ U, badU u) ∪ (⋃ w ∈ W, badW w)
  let rectangleFailure := ⋃ AB ∈ tests, bad AB
  have hfinite {β : Type _} (t : Finset β) (f : β → Set (I → Bool))
      (b : ℝ) (hf : ∀ i ∈ t, μ.real (f i) ≤ b) :
      μ.real (⋃ i ∈ t, f i) ≤ t.card * b := by
    calc
      _ ≤ ∑ i ∈ t, μ.real (f i) := measureReal_biUnion_finset_le t f
      _ ≤ ∑ _i ∈ t, b := Finset.sum_le_sum hf
      _ = t.card * b := by simp [nsmul_eq_mul]
  have hdfail : μ.real degreeFailure < 1 / 4 := by
    calc
      _ ≤ μ.real (⋃ u ∈ U, badU u) + μ.real (⋃ w ∈ W, badW w) :=
        measureReal_union_le _ _
      _ ≤ (U.card : ℝ) * (2 * Real.exp (-c ^ 2 * (n : ℝ) / 8)) +
          W.card * (2 * Real.exp (-c ^ 2 * (n : ℝ) / 8)) :=
        add_le_add (hfinite U badU _ (fun u _ => htailU u))
          (hfinite W badW _ (fun w _ => htailW w))
      _ = 4 * n * Real.exp (-c ^ 2 * (n : ℝ) / 8) := by rw [hU, hW]; ring
      _ < 1 / 4 := hdegreeCut
  have hrfail : μ.real rectangleFailure < 1 / 4 := by
    calc
      _ ≤ (tests.card : ℝ) * (2 * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8)) :=
        hfinite tests bad _ (fun AB _ => htail AB)
      _ = 2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) := by
        rw [htests]
        ring
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
  have hgoodU (u) (hu : u ∈ U) : |∑ e ∈ s {u} W, Y e ω| ≤ c * n / 4 := by
    apply le_of_not_gt
    intro hb
    apply hgood
    exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hb⟩⟩))
  have hgoodW (w) (hw : w ∈ W) : |∑ e ∈ s U {w}, Y e ω| ≤ c * n / 4 := by
    apply le_of_not_gt
    intro hb
    apply hgood
    exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hb⟩⟩))
  refine ⟨H ω, inferInstance, hcontain ω, ?_, ?_, ?_⟩
  · intro u hu
    have hcount' := hcount {u} W (Finset.singleton_subset_iff.mpr hu)
      (Finset.Subset.refl _) ω
    rw [hrowcard (H ω) u] at hcount'
    have hb := (abs_le.mp (hgoodU u hu)).1
    simp only [Y, Finset.sum_sub_distrib] at hb
    have hm := hrowmean u hu
    rw [← hcount'] at hb
    change (7 * c / 4) * n ≤ _
    linarith only [hb, hm]
  · intro w hw
    have hcount' := hcount U {w} (Finset.Subset.refl _)
      (Finset.singleton_subset_iff.mpr hw) ω
    rw [hcolcard (H ω) w] at hcount'
    have hb := (abs_le.mp (hgoodW w hw)).1
    simp only [Y, Finset.sum_sub_distrib] at hb
    have hm := hcolmean w hw
    rw [← hcount'] at hb
    change (7 * c / 4) * n ≤ _
    linarith only [hb, hm]
  · intro A hAU B hBW hA hB
    have hm : (A, B) ∈ tests := Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hAU, Finset.mem_powerset.mpr hBW⟩
    have hb : |∑ e ∈ s A B, Y e ω| ≤ (h / 4) * A.card * B.card := by
      apply le_of_not_gt
      intro hb
      apply hgood
      exact Or.inr (Set.mem_iUnion.mpr ⟨(A, B), Set.mem_iUnion.mpr ⟨hm, hA, hB, hb⟩⟩)
    have hsample : |(((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ) -
        ∑ e ∈ A.product B, p e| ≤ (h / 4) * A.card * B.card := by
      rw [hcount A B hAU hBW ω, ← hmean A B hAU hBW]
      simpa only [Y, Finset.sum_sub_distrib] using hb
    have hex := hexpect A hAU B hBW hA hB
    have hdiscrep : |(((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ) -
        d * A.card * B.card| < (h / 2) * A.card * B.card := by
      have ht := abs_sub_le
        (((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ)
        (∑ e ∈ A.product B, p e) (d * A.card * B.card)
      linarith only [ht, hsample, hex]
    have hAp : 0 < (A.card : ℝ) := (mul_pos hh hnr).trans hA
    have hBp : 0 < (B.card : ℝ) := (mul_pos hh hnr).trans hB
    have hden : 0 < (A.card : ℝ) * B.card := mul_pos hAp hBp
    have hid : ((H ω).edgeDensity A B : ℝ) - d =
        ((((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ) -
          d * A.card * B.card) / ((A.card : ℝ) * B.card) := by
      simp only [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def,
        Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Finset.product_eq_sprod]
      field_simp
    rw [hid, abs_div, abs_of_pos hden]
    apply (div_lt_iff₀ hden).mpr
    simpa only [mul_assoc] using hdiscrep
