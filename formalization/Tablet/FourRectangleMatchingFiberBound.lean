import Tablet.PerfectMatching
import Tablet.FourRectangleMatchingPartition
import Tablet.MatchingPartitionRestrictionCount
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin

-- [TABLET NODE: FourRectangleMatchingFiberBound]
theorem FourRectangleMatchingFiberBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W S T : Finset V) (hUW : Disjoint U W) (n x : ℕ)
    (hU : U.card = n) (hW : W.card = n) (hS : S ⊆ U) (hT : T ⊆ W)
    (hxS : x ≤ S.card) (hxT : x ≤ T.card)
    (hfit : T.card - x ≤ n - S.card) (K : ℕ → ℝ)
    (hK : ∀ y ≤ n, 0 ≤ K y)
    (hbound : ∀ (A B : Finset V) (hAB : Disjoint A B) (y : ℕ),
      A ⊆ U → B ⊆ W → A.card = y → B.card = y →
      ({f : A → B | PerfectMatching G A B hAB f}.ncard : ℝ) ≤ K y) :
    ({f : U → W | PerfectMatching G U W hUW f ∧
      (Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f u).1 ∈ T).card = x}.ncard : ℝ) ≤
    (S.card.choose x : ℝ) * (T.card.choose x : ℝ) *
      ((n - T.card).choose (S.card - x) : ℝ) *
      ((n - S.card).choose (T.card - x) : ℝ) *
      (K x * K (S.card - x) * K (T.card - x) * K (n - S.card - (T.card - x))) := by
-- BODY
  classical
  -- The coordinates of a choice are (A, B, C, E).
  let choices := (S.powersetCard x).product
    ((T.powersetCard x).product
      (((W \ T).powersetCard (S.card - x)).product
        ((U \ S).powersetCard (T.card - x))))
  let L : choices → Fin 4 → Finset V := fun q =>
    ![q.1.1, S \ q.1.1, q.1.2.2.2, U \ (S ∪ q.1.2.2.2)]
  let R : choices → Fin 4 → Finset V := fun q =>
    ![q.1.2.1, q.1.2.2.1, T \ q.1.2.1, W \ (T ∪ q.1.2.2.1)]
  let y : Fin 4 → ℕ := ![x, S.card - x, T.card - x, n - S.card - (T.card - x)]
  have hp (q : choices) :
      (q.1.1 ⊆ S ∧ q.1.1.card = x) ∧
      (q.1.2.1 ⊆ T ∧ q.1.2.1.card = x) ∧
      (q.1.2.2.1 ⊆ W \ T ∧ q.1.2.2.1.card = S.card - x) ∧
      (q.1.2.2.2 ⊆ U \ S ∧ q.1.2.2.2.card = T.card - x) := by
    have h := Finset.mem_product.mp q.2
    have h' := Finset.mem_product.mp h.2
    have h'' := Finset.mem_product.mp h'.2
    exact ⟨Finset.mem_powersetCard.mp h.1, Finset.mem_powersetCard.mp h'.1,
      Finset.mem_powersetCard.mp h''.1, Finset.mem_powersetCard.mp h''.2⟩
  have hL (q : choices) (i : Fin 4) : L q i ⊆ U := by
    fin_cases i
    · exact (hp q).1.1.trans hS
    · exact Finset.sdiff_subset.trans hS
    · exact (hp q).2.2.2.1.trans Finset.sdiff_subset
    · exact Finset.sdiff_subset
  have hR (q : choices) (i : Fin 4) : R q i ⊆ W := by
    fin_cases i
    · exact (hp q).2.1.1.trans hT
    · exact (hp q).2.2.1.1.trans Finset.sdiff_subset
    · exact Finset.sdiff_subset.trans hT
    · exact Finset.sdiff_subset
  have horders (q : choices) (i : Fin 4) :
      (L q i).card = y i ∧ (R q i).card = y i := by
    obtain ⟨hA, hB, hC, hE⟩ := hp q
    have hEU := hE.1.trans Finset.sdiff_subset
    have hCW := hC.1.trans Finset.sdiff_subset
    have hSE : Disjoint S q.1.2.2.2 := by
      apply Finset.disjoint_left.mpr
      intro u huS huE
      exact (Finset.mem_sdiff.mp (hE.1 huE)).2 huS
    have hTC : Disjoint T q.1.2.2.1 := by
      apply Finset.disjoint_left.mpr
      intro u huT huC
      exact (Finset.mem_sdiff.mp (hC.1 huC)).2 huT
    fin_cases i
    · exact ⟨hA.2, hB.2⟩
    · refine ⟨?_, hC.2⟩
      change (S \ q.1.1).card = S.card - x
      rw [Finset.card_sdiff_of_subset hA.1, hA.2]
    · refine ⟨hE.2, ?_⟩
      change (T \ q.1.2.1).card = T.card - x
      rw [Finset.card_sdiff_of_subset hB.1, hB.2]
    · constructor
      · change (U \ (S ∪ q.1.2.2.2)).card = n - S.card - (T.card - x)
        rw [Finset.card_sdiff_of_subset (Finset.union_subset hS hEU), hU,
          Finset.card_union_of_disjoint hSE, hE.2, Nat.sub_add_eq]
      · change (W \ (T ∪ q.1.2.2.1)).card = n - S.card - (T.card - x)
        rw [Finset.card_sdiff_of_subset (Finset.union_subset hT hCW), hW,
          Finset.card_union_of_disjoint hTC, hC.2]
        omega
  have hy (i : Fin 4) : y i ≤ n := by
    have hs := Finset.card_le_card hS
    have ht := Finset.card_le_card hT
    fin_cases i <;> dsimp [y] <;> omega
  have hcover (q : choices) (u : V) (hu : u ∈ U) : ∃ i, u ∈ L q i := by
    by_cases huS : u ∈ S
    · by_cases huA : u ∈ q.1.1
      · exact ⟨0, huA⟩
      · exact ⟨1, Finset.mem_sdiff.mpr ⟨huS, huA⟩⟩
    · by_cases huE : u ∈ q.1.2.2.2
      · exact ⟨2, huE⟩
      · exact ⟨3, Finset.mem_sdiff.mpr ⟨hu, by simpa only [Finset.mem_union,
          not_or] using (And.intro huS huE)⟩⟩
  let fiber := fun q : choices => {f : U → W | PerfectMatching G U W hUW f ∧
    ∀ i, ((L q i).attach.image fun u => (f ⟨u.1, hL q i u.2⟩).1) = R q i}
  let counted := {f : U → W | PerfectMatching G U W hUW f ∧
    (Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f u).1 ∈ T).card = x}
  have hencode (f : counted) : ∃ q : choices, f.1 ∈ fiber q := by
    -- Extend to ambient vertices for finset images; only values on U matter.
    let F : V → V := fun u => if hu : u ∈ U then (f.1 ⟨u, hu⟩).1 else u
    have hFu (u : U) : F u.1 = (f.1 u).1 := by simp [F, u.2]
    have hF : Set.BijOn F (U : Set V) (W : Set V) := by
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro u hu
        rw [hFu ⟨u, hu⟩]
        exact (f.1 ⟨u, hu⟩).2
      · intro u hu v hv huv
        have heq : f.1 ⟨u, hu⟩ = f.1 ⟨v, hv⟩ :=
          Subtype.ext ((hFu ⟨u, hu⟩).symm.trans (huv.trans (hFu ⟨v, hv⟩)))
        exact congrArg (fun a : U => a.1) (f.2.1.1.1 heq)
      · intro v hv
        obtain ⟨u, hu⟩ := f.2.1.1.2 ⟨v, hv⟩
        exact ⟨u.1, u.2, (hFu u).trans (congrArg (fun b : W => b.1) hu)⟩
    have hx : (S.filter fun u => F u ∈ T).card = x := by
      rw [← f.2.2]
      symm
      apply Finset.card_bij (fun u _ => u.1)
      · intro u hu
        obtain ⟨_, huS, huT⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨huS, (hFu u).symm ▸ huT⟩
      · intro u hu v hv huv
        exact Subtype.ext huv
      · intro v hv
        obtain ⟨hvS, hvT⟩ := Finset.mem_filter.mp hv
        refine ⟨⟨v, hS hvS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, ?_⟩, rfl⟩
        simpa only [F, dif_pos (hS hvS)] using hvT
    obtain ⟨hA, hB, hC, hE, hEi, hDi, hSc, hTc, hDc, hRc, hpartL, hpartR⟩ :=
      FourRectangleMatchingPartition U W S T F hF hS hT n x hU hW hx
    let A := S.filter fun u => F u ∈ T
    let B := A.image F
    let C := (S \ A).image F
    let E := U.filter fun u => F u ∈ T \ B
    let q : choices := ⟨(A, B, C, E), by
      exact Finset.mem_product.mpr ⟨hA, Finset.mem_product.mpr
        ⟨hB, Finset.mem_product.mpr ⟨hC, hE⟩⟩⟩⟩
    refine ⟨q, f.2.1, ?_⟩
    intro i
    have himage : ((L q i).attach.image fun u =>
        (f.1 ⟨u.1, hL q i u.2⟩).1) = (L q i).image F := by
      ext v
      simp only [Finset.mem_image, Finset.mem_attach, true_and]
      constructor
      · rintro ⟨u, hu⟩
        exact ⟨u.1, u.2, (hFu ⟨u.1, hL q i u.2⟩).trans hu⟩
      · rintro ⟨u, hu, huv⟩
        exact ⟨⟨u, hu⟩, (hFu ⟨u, hL q i hu⟩).symm.trans huv⟩
    rw [himage]
    fin_cases i
    · rfl
    · rfl
    · exact hEi
    · exact hDi
  have hfiber (q : choices) : ((fiber q).ncard : ℝ) ≤ ∏ i, K (y i) := by
    let P := fun i => {g : L q i → R q i |
      PerfectMatching G (L q i) (R q i) (hUW.mono (hL q i) (hR q i)) g}
    have hcount : (fiber q).ncard ≤ ∏ i, (P i).ncard :=
      MatchingPartitionRestrictionCount G U W hUW (L q) (R q) (hL q) (hR q) (hcover q)
    have hb (i : Fin 4) : ((P i).ncard : ℝ) ≤ K (y i) :=
      hbound (L q i) (R q i) (hUW.mono (hL q i) (hR q i))
        (y i) (hL q i) (hR q i) (horders q i).1 (horders q i).2
    have h01 : ((P 0).ncard : ℝ) * ((P 1).ncard : ℝ) ≤ K (y 0) * K (y 1) :=
      mul_le_mul (hb 0) (hb 1) (Nat.cast_nonneg _) (hK _ (hy 0))
    have h012 : ((P 0).ncard : ℝ) * ((P 1).ncard : ℝ) * ((P 2).ncard : ℝ) ≤
        K (y 0) * K (y 1) * K (y 2) :=
      mul_le_mul h01 (hb 2) (Nat.cast_nonneg _)
        (mul_nonneg (hK _ (hy 0)) (hK _ (hy 1)))
    calc
      ((fiber q).ncard : ℝ) ≤ ((∏ i, (P i).ncard : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = ∏ i, ((P i).ncard : ℝ) := by rw [Nat.cast_prod]
      _ ≤ ∏ i, K (y i) := by
        rw [Fin.prod_univ_four, Fin.prod_univ_four]
        exact mul_le_mul h012 (hb 3) (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (hK _ (hy 0)) (hK _ (hy 1))) (hK _ (hy 2)))
  let encode : counted → Σ q : choices, fiber q := fun f =>
    ⟨(hencode f).choose, ⟨f.1, (hencode f).choose_spec⟩⟩
  have hinj : Function.Injective encode := by
    intro f g hfg
    exact Subtype.ext (congrArg (fun z : Σ q : choices, fiber q => z.2.1) hfg)
  have htotal : counted.ncard ≤ ∑ q : choices, (fiber q).ncard := by
    have h := Fintype.card_le_of_injective encode hinj
    simpa only [Fintype.card_sigma, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using h
  have hsum : (counted.ncard : ℝ) ≤ (choices.card : ℝ) * (∏ i, K (y i)) := by
    calc
      (counted.ncard : ℝ) ≤ ((∑ q : choices, (fiber q).ncard : ℕ) : ℝ) := by
        exact_mod_cast htotal
      _ = ∑ q : choices, ((fiber q).ncard : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ _q : choices, ∏ i, K (y i) := Finset.sum_le_sum fun q _ => hfiber q
      _ = (choices.card : ℝ) * (∏ i, K (y i)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hc : choices.card = S.card.choose x * T.card.choose x *
      (n - T.card).choose (S.card - x) * (n - S.card).choose (T.card - x) := by
    simp only [choices, Finset.product_eq_sprod, Finset.card_product, Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hT, Finset.card_sdiff_of_subset hS, hU, hW]
    ac_rfl
  change (counted.ncard : ℝ) ≤ _
  convert hsum using 1
  rw [hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Fin.prod_univ_four]
  rfl
