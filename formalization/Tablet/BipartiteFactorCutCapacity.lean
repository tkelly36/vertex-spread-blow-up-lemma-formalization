import Tablet.BipartiteFactorNetwork

open scoped BigOperators

-- [TABLET NODE: BipartiteFactorCutCapacity]
theorem BipartiteFactorCutCapacity {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (k : ℕ) :
    (∑ w, ((BipartiteFactorNetwork G U W k).capacity
      (BipartiteFactorNetwork G U W k).source w : ℤ)) = (k * U.card : ℕ) ∧
    ∀ S : Finset (Option U ⊕ Option W),
      (BipartiteFactorNetwork G U W k).source ∈ S →
      (BipartiteFactorNetwork G U W k).sink ∉ S →
      ∃ A B : Finset V, A ⊆ U ∧ B ⊆ W ∧
        (∑ v ∈ S, ∑ w ∈ Finset.univ \ S,
          ((BipartiteFactorNetwork G U W k).capacity v w : ℤ)) =
        ((k * A.card +
          (((U \ A) ×ˢ (W \ B)).filter fun p => G.Adj p.1 p.2).card +
          k * B.card : ℕ) : ℤ) := by
-- BODY
  classical
  constructor
  · simp [Fintype.sum_sum_type, Fintype.sum_option, BipartiteFactorNetwork, mul_comm]
  · intro S hs ht
    let A := U.filter fun u => ∀ hu : u ∈ U, (Sum.inl (some ⟨u, hu⟩) : Option U ⊕ Option W) ∉ S
    let B := W.filter fun w => ∀ hw : w ∈ W, (Sum.inr (some ⟨w, hw⟩) : Option U ⊕ Option W) ∈ S
    have hA : A ⊆ U := Finset.filter_subset _ _
    have hB : B ⊆ W := Finset.filter_subset _ _
    have ha (u : U) : u.val ∈ A ↔ (Sum.inl (some u) : Option U ⊕ Option W) ∉ S := by
      simp [A, u.property]
    have hb (w : W) : w.val ∈ B ↔ (Sum.inr (some w) : Option U ⊕ Option W) ∈ S := by
      simp [B, w.property]
    have hal (u : U) : (Sum.inl (some u) : Option U ⊕ Option W) ∈ S ↔ u.val ∉ A := by
      simpa only [not_not] using (not_congr (ha u)).symm
    have hbr (w : W) : (Sum.inr (some w) : Option U ⊕ Option W) ∉ S ↔ w.val ∉ B :=
      (not_congr (hb w)).symm
    have hcard (T D : Finset V) (hD : D ⊆ T) :
        (∑ v : T, if v.val ∈ D then (1 : ℤ) else 0) = (D.card : ℤ) := by
      rw [Finset.sum_coe_sort T (fun v : V => if v ∈ D then (1 : ℤ) else 0)]
      have he : T.filter (fun v => v ∈ D) = D := by
        ext v
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hD h, h⟩⟩
      rw [← Finset.sum_filter, he]
      simp
    have hca : (∑ u : U, if (Sum.inl (some u) : Option U ⊕ Option W) ∉ S then (k : ℤ) else 0) =
        ((k * A.card : ℕ) : ℤ) := by
      simp_rw [← ha]
      calc
        _ = (k : ℤ) * ∑ u : U, if u.val ∈ A then (1 : ℤ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          split_ifs <;> simp
        _ = _ := by rw [hcard U A hA, Nat.cast_mul]
    have hcb : (∑ w : W, if (Sum.inr (some w) : Option U ⊕ Option W) ∈ S then (k : ℤ) else 0) =
        ((k * B.card : ℕ) : ℤ) := by
      simp_rw [← hb]
      calc
        _ = (k : ℤ) * ∑ w : W, if w.val ∈ B then (1 : ℤ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w hw
          split_ifs <;> simp
        _ = _ := by rw [hcard W B hB, Nat.cast_mul]
    have hmiddle : (∑ u : U, ∑ w : W,
        if (Sum.inl (some u) : Option U ⊕ Option W) ∈ S ∧
          (Sum.inr (some w) : Option U ⊕ Option W) ∉ S ∧ G.Adj u.val w.val
        then (1 : ℤ) else 0) =
        ((((U \ A) ×ˢ (W \ B)).filter fun p => G.Adj p.1 p.2).card : ℤ) := by
      simp_rw [hal, hbr]
      rw [Finset.sum_coe_sort U (fun u : V => ∑ w : W,
        if u ∉ A ∧ w.val ∉ B ∧ G.Adj u w.val then (1 : ℤ) else 0)]
      have hr (u : V) : (∑ w : W,
          if u ∉ A ∧ w.val ∉ B ∧ G.Adj u w.val then (1 : ℤ) else 0) =
          ∑ w ∈ W, if u ∉ A ∧ w ∉ B ∧ G.Adj u w then (1 : ℤ) else 0 :=
        Finset.sum_coe_sort W (fun w : V =>
          if u ∉ A ∧ w ∉ B ∧ G.Adj u w then (1 : ℤ) else 0)
      simp_rw [hr]
      change (∑ u ∈ U, ∑ w ∈ W,
        if u ∉ A ∧ w ∉ B ∧ G.Adj u w then (1 : ℤ) else 0) =
        (((((U \ A).product (W \ B)).filter fun p => G.Adj p.1 p.2).card : ℕ) : ℤ)
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Finset.sdiff_eq_filter, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      rw [Finset.product_eq_sprod, Finset.sum_product]
      simp only [Finset.sum_filter]
    let H := fun v w : Option U ⊕ Option W =>
      if v ∈ S ∧ w ∉ S then ((BipartiteFactorNetwork G U W k).capacity v w : ℤ) else 0
    have hsum (T : Finset (Option U ⊕ Option W)) (a : (Option U ⊕ Option W) → ℤ) :
        (∑ v ∈ T, a v) = ∑ v, if v ∈ T then a v else 0 := by
      have he : Finset.univ.filter (fun v => v ∈ T) = T := by ext v; simp
      rw [← Finset.sum_filter, he]
    have hconvert : (∑ v ∈ S, ∑ w ∈ Finset.univ \ S,
        ((BipartiteFactorNetwork G U W k).capacity v w : ℤ)) = ∑ v, ∑ w, H v w := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvS : v ∈ S
      · rw [if_pos hvS, hsum]
        apply Finset.sum_congr rfl
        intro w hw
        simp [H, hvS]
      · simp [H, hvS]
    refine ⟨A, B, hA, hB, ?_⟩
    rw [hconvert]
    have hcalc : (∑ v, ∑ w, H v w) =
        (∑ u : U, if (Sum.inl (some u) : Option U ⊕ Option W) ∉ S then (k : ℤ) else 0) +
        (∑ u : U, ∑ w : W,
          if (Sum.inl (some u) : Option U ⊕ Option W) ∈ S ∧
            (Sum.inr (some w) : Option U ⊕ Option W) ∉ S ∧ G.Adj u.val w.val
          then (1 : ℤ) else 0) +
        (∑ w : W, if (Sum.inr (some w) : Option U ⊕ Option W) ∈ S then (k : ℤ) else 0) := by
      change (Sum.inl none : Option U ⊕ Option W) ∈ S at hs
      change (Sum.inr none : Option U ⊕ Option W) ∉ S at ht
      simp only [Fintype.sum_sum_type, Fintype.sum_option]
      simp [H, BipartiteFactorNetwork,
        hs, ht, ite_and, Finset.sum_ite_irrel, add_assoc]
    rw [hcalc, hca, hcb, hmiddle]
    simp only [Nat.cast_add]
