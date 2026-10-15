import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.FiniteIndependentSubgaussianTail
import Mathlib.Combinatorics.SimpleGraph.Density

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- [TABLET NODE: SimultaneousUnequalRetention]
theorem SimultaneousUnequalRetention
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (n : ℕ) (h : ℝ) (hn : 0 < n) (hh : 0 < h)
    (hU : U.card = n) (hW : W.card = n) (hUW : Disjoint U W)
    (p : V × V → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hzero : ∀ e, ¬G.Adj e.1 e.2 → p e = 0)
    (hcut : 2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj,
      H ≤ G ∧
      (∀ u ∈ U, ∀ w ∈ W, G.Adj u w → p (u, w) = 1 → H.Adj u w) ∧
      (∀ A ⊆ U, ∀ B ⊆ W, h * n < (A.card : ℝ) →
        h * n < (B.card : ℝ) →
        |(((A.product B).filter fun e => H.Adj e.1 e.2).card : ℝ) -
          ∑ e ∈ A.product B, p e| ≤ (h / 4) * A.card * B.card) := by
-- BODY
  classical
  let E := (U.product W).filter fun e => G.Adj e.1 e.2
  let I := {e // e ∈ E}
  let q : I → ℝ≥0 := fun e => ⟨p e.val, (hp e.val).1⟩
  have hq : ∀ e, q e ≤ 1 := fun e => by exact_mod_cast (hp e.val).2
  let μ := Measure.pi (fun e => (PMF.bernoulli (q e) (hq e)).toMeasure)
  obtain ⟨hμ, hi, he, hs⟩ := IndependentUnequalEdgeSampleLaw q hq
  change IsProbabilityMeasure μ at hμ
  letI := hμ
  let X : I → (I → Bool) → ℝ := fun e ω => if ω e then 1 else 0
  let Y : I → (I → Bool) → ℝ := fun e ω => X e ω - p e.val
  have hind : iIndepFun Y μ := by
    exact hi.comp (fun e x => x - p e.val) (fun _ => measurable_id.sub_const _)
  have hsg : ∀ e, HasSubgaussianMGF (Y e) (1 / 4) μ := hs
  let H : (I → Bool) → SimpleGraph V := fun ω =>
    { Adj := fun u w => G.Adj u w ∧
        ((∃ he : (u, w) ∈ E, ω ⟨(u, w), he⟩ = true) ∨
         (∃ he : (w, u) ∈ E, ω ⟨(w, u), he⟩ = true))
      symm := by
        intro u w huv
        exact ⟨huv.1.symm, huv.2.symm⟩
      loopless := ⟨fun u huu => G.loopless.irrefl u huu.1⟩ }
  have hcontain (ω) : H ω ≤ G := fun _ _ huv => huv.1
  have hcross (ω : I → Bool) (u) (hu : u ∈ U) (w) (hw : w ∈ W) :
      (H ω).Adj u w ↔ ∃ he : (u, w) ∈ E, ω ⟨(u, w), he⟩ = true := by
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
      have heE : e ∈ E := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hAU heA, hBW heB⟩, heG⟩
      exact ⟨⟨e, heE⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heAB⟩, rfl⟩
    · intro e hem
      rfl
  have hcount (A B : Finset V) (hAU : A ⊆ U) (hBW : B ⊆ W) (ω : I → Bool) :
      (((A.product B).filter fun e => (H ω).Adj e.1 e.2).card : ℝ) =
        ∑ e ∈ s A B, X e ω := by
    let f : V × V → ℝ := fun e => if he : e ∈ E then X ⟨e, he⟩ ω else 0
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
      have hnE : e ∉ E := fun heE => hg (Finset.mem_filter.mp heE).2
      exact hf (dif_neg hnE)
    rw [hfull, ← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e hem
    obtain ⟨heA, heB⟩ := Finset.mem_product.mp hem
    have hc := hcross ω e.1 (hAU heA) e.2 (hBW heB)
    by_cases heE : e ∈ E
    · simp only [f, dif_pos heE, X]
      have hc' : (H ω).Adj e.1 e.2 ↔ ω ⟨e, heE⟩ = true := by
        refine ⟨fun hadj => ?_, fun hω => hc.mpr ⟨heE, hω⟩⟩
        obtain ⟨heE', hω⟩ := hc.mp hadj
        exact hω
      simp only [hc']
    · have hnot : ¬(H ω).Adj e.1 e.2 := fun hadj =>
        (hc.mp hadj).elim (fun he _ => heE he)
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
  let bad : Finset V × Finset V → Set (I → Bool) := fun AB =>
    {ω | h * n < (AB.1.card : ℝ) ∧ h * n < (AB.2.card : ℝ) ∧
      (h / 4) * AB.1.card * AB.2.card < |∑ e ∈ s AB.1 AB.2, Y e ω|}
  have htail (AB : Finset V × Finset V) :
      μ.real (bad AB) ≤ 2 * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) := by
    by_cases hA : h * n < (AB.1.card : ℝ)
    · by_cases hB : h * n < (AB.2.card : ℝ)
      · let N : ℝ := (AB.1.card : ℝ) * AB.2.card
        have hhn : 0 < h * (n : ℝ) := mul_pos hh (by exact_mod_cast hn)
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
          <;> ring
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
  let failure := ⋃ AB ∈ tests, bad AB
  have hfail : μ.real failure < 1 := by
    calc
      μ.real failure ≤ ∑ AB ∈ tests, μ.real (bad AB) :=
        measureReal_biUnion_finset_le tests bad
      _ ≤ ∑ _AB ∈ tests, 2 * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) :=
        Finset.sum_le_sum (fun AB _ => htail AB)
      _ = 2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) := by
        rw [Finset.sum_const, nsmul_eq_mul, htests]
        ring
      _ < 1 := hcut
  have hone : ∀ᵐ ω ∂μ, ∀ e : I, p e.val = 1 → ω e = true := by
    apply ae_all_iff.mpr
    intro e
    by_cases hpone : p e.val = 1
    · have hm : MeasurableSet {ω : I → Bool | ω e = true} :=
        measurableSet_eq_fun (measurable_pi_apply e) measurable_const
      have hiint : (∫ ω, X e ω ∂μ) = μ.real {ω : I → Bool | ω e = true} := by
        have hfun : X e = {ω : I → Bool | ω e = true}.indicator (fun _ => (1 : ℝ)) := by
          ext ω
          simp only [X, Set.indicator, Set.mem_setOf_eq]
        rw [hfun]
        exact integral_indicator_one hm
      have hprob : μ.real {ω : I → Bool | ω e = true} = 1 := by
        rw [← hiint]
        exact (he e).trans hpone
      have hnull : μ {ω : I → Bool | ω e ≠ true} = 0 := by
        apply (measureReal_eq_zero_iff).mp
        change μ.real {ω : I → Bool | ω e = true}ᶜ = 0
        rw [probReal_compl_eq_one_sub hm, hprob, sub_self]
      have ha : ∀ᵐ ω ∂μ, ω e = true := ae_iff.mpr hnull
      exact ha.mono (fun ω hω _ => hω)
    · exact Filter.Eventually.of_forall (fun ω h => False.elim (hpone h))
  obtain ⟨ω, hgood, hωone⟩ : ∃ ω, ω ∉ failure ∧
      ∀ e : I, p e.val = 1 → ω e = true := by
    have hm : MeasurableSet failure := by
      exact Set.to_countable failure |>.measurableSet
    have hpos : μ failureᶜ ≠ 0 := by
      apply (measureReal_eq_zero_iff).not.mp
      rw [probReal_compl_eq_one_sub hm]
      linarith only [hfail]
    obtain ⟨ω, hω, hωone⟩ := μ.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hone)
    exact ⟨ω, hω, hωone⟩
  refine ⟨H ω, inferInstance, hcontain ω, ?_, ?_⟩
  · intro u hu w hw huw hpone
    have hem : (u, w) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hw⟩, huw⟩
    exact (hcross ω u hu w hw).mpr ⟨hem, hωone ⟨(u, w), hem⟩ hpone⟩
  · intro A hAU B hBW hA hB
    have hm : (A, B) ∈ tests := Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hAU, Finset.mem_powerset.mpr hBW⟩
    have hnobad : ω ∉ bad (A, B) := fun hb =>
      hgood (Set.mem_iUnion.mpr ⟨(A, B), Set.mem_iUnion.mpr ⟨hm, hb⟩⟩)
    have hb : |∑ e ∈ s A B, Y e ω| ≤ (h / 4) * A.card * B.card := by
      by_contra! hb
      exact hnobad ⟨hA, hB, hb⟩
    rw [hcount A B hAU hBW ω, ← hmean A B hAU hBW]
    simpa only [Y, Finset.sum_sub_distrib] using hb
