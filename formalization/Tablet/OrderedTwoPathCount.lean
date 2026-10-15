import Tablet.Preamble

-- [TABLET NODE: OrderedTwoPathCount]
theorem OrderedTwoPathCount {A B : Type*} [DecidableEq A] [DecidableEq B]
    (U : Finset A) (W : Finset B) (P : A → B → Prop) [DecidableRel P] :
    (∑ u ∈ U, (W.filter fun w => P u w).card ^ 2) =
      ∑ z ∈ W ×ˢ W, (U.filter fun u => P u z.1 ∧ P u z.2).card := by
-- BODY
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, pow_two,
    Finset.sum_mul_sum, Finset.sum_product]
  calc
    _ = ∑ w ∈ W, ∑ u ∈ U, ∑ z ∈ W,
        (if P u w then 1 else 0) * (if P u z then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ w ∈ W, ∑ z ∈ W, ∑ u ∈ U,
        (if P u w then 1 else 0) * (if P u z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> simp_all
