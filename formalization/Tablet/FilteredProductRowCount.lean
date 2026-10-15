import Tablet.Preamble

-- [TABLET NODE: FilteredProductRowCount]
theorem FilteredProductRowCount {A B : Type*} [DecidableEq A] [DecidableEq B]
    (U : Finset A) (W : Finset B) (P : A → B → Prop) [DecidableRel P] :
    ((U.product W).filter fun p => P p.1 p.2).card =
      ∑ x ∈ U, (W.filter fun y => P x y).card := by
-- BODY
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_product U W (fun p => if P p.1 p.2 then 1 else 0)
