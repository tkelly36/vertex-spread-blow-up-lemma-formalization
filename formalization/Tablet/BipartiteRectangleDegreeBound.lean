import Tablet.FilteredProductRowCount

open scoped BigOperators

-- [TABLET NODE: BipartiteRectangleDegreeBound]
theorem BipartiteRectangleDegreeBound {V : Type*} [DecidableEq V]
    (U W : Finset V) (P : V → V → Prop) [DecidableRel P] (k : ℕ)
    (hrow : ∀ u ∈ U, k ≤ (W.filter fun w => P u w).card)
    (hcol : ∀ w ∈ W, (U.filter fun u => P u w).card ≤ k)
    (A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W) :
    k * (A.card + B.card - W.card) ≤
      ((A ×ˢ B).filter fun p => P p.1 p.2).card := by
-- BODY
  classical
  let e := fun X Y : Finset V => ((X ×ˢ Y).filter fun p => P p.1 p.2).card
  have hlow : k * A.card ≤ e A W := by
    change k * A.card ≤ ((A.product W).filter fun p => P p.1 p.2).card
    rw [FilteredProductRowCount]
    calc
      k * A.card = ∑ u ∈ A, k := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ A, (W.filter fun w => P u w).card :=
        Finset.sum_le_sum fun u hu => hrow u (hA hu)
  have htranspose : e A (W \ B) =
      ∑ w ∈ W \ B, (A.filter fun u => P u w).card := by
    simp only [e, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
    exact Finset.sum_comm
  have hhigh : e A (W \ B) ≤ k * (W.card - B.card) := by
    rw [htranspose]
    calc
      (∑ w ∈ W \ B, (A.filter fun u => P u w).card) ≤
          ∑ w ∈ W \ B, k := by
        apply Finset.sum_le_sum
        intro w hw
        exact (Finset.card_le_card (Finset.filter_subset_filter _ hA)).trans
          (hcol w (Finset.mem_sdiff.mp hw).1)
      _ = k * (W.card - B.card) := by
        simp [Finset.card_sdiff_of_subset hB, Nat.mul_comm]
  have hsplit : e A (W \ B) + e A B = e A W := by
    change ((A.product (W \ B)).filter fun p => P p.1 p.2).card +
      ((A.product B).filter fun p => P p.1 p.2).card =
      ((A.product W).filter fun p => P p.1 p.2).card
    rw [FilteredProductRowCount, FilteredProductRowCount, FilteredProductRowCount,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_sdiff (f := fun w => if P u w then 1 else 0) hB
  have hb := Finset.card_le_card hB
  by_cases hab : W.card ≤ A.card + B.card
  · have hd : A.card = (A.card + B.card - W.card) + (W.card - B.card) := by omega
    have hm := congrArg (fun x : ℕ => k * x) hd
    simp only [Nat.mul_add] at hm
    dsimp only [e] at hsplit hlow hhigh
    omega
  · have hz : A.card + B.card - W.card = 0 := by omega
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
