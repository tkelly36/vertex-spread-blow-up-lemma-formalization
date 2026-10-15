import Tablet.ProductPermutationSubsetLaw
import Tablet.UniformSubsetIntersectionLaw
import Tablet.HypergeometricTwoTail

open scoped Classical BigOperators

-- [TABLET NODE: ProductPermutationIntersectionTail]
theorem ProductPermutationIntersectionTail {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → Type*) [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (i : I) (S T : Finset (F i)) (n : ℕ) (hcard : Fintype.card (F i) = n)
    (hn : 0 < n) (a : ℝ) (ha : 0 < a) :
    (((Finset.univ : Finset (∀ j, Equiv.Perm (F j))).filter
      fun (ω : ∀ j, Equiv.Perm (F j)) =>
        a * n < |(((S.image (ω i)) ∩ T).card : ℝ) - (S.card : ℝ) * T.card / n|).card : ℝ) /
        (Fintype.card (∀ j, Equiv.Perm (F j)) : ℝ) ≤
      2 * Real.exp (-(a ^ 2 / (2 * (1 + a / 3))) * n) := by
-- BODY
  classical
  let K := (Finset.univ : Finset (F i)).powersetCard S.card
  let E := (Finset.range (n + 1)).filter
    fun x : ℕ => a * n < |(x : ℝ) - (S.card : ℝ) * T.card / n|
  have hS : S.card ≤ n := by
    simpa only [Finset.card_univ, hcard] using
      (Finset.card_le_card (Finset.subset_univ S))
  have hT : T.card ≤ n := by
    simpa only [Finset.card_univ, hcard] using
      (Finset.card_le_card (Finset.subset_univ T))
  have hcount : (K.filter fun U =>
        a * n < |((U ∩ T).card : ℝ) - (S.card : ℝ) * T.card / n|).card =
      ∑ x ∈ E, (K.filter fun U => (U ∩ T).card = x).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_congr
    intro U _
    have hbound : (U ∩ T).card < n + 1 :=
      Nat.lt_succ_of_le ((Finset.card_le_card Finset.inter_subset_right).trans hT)
    simp only [E, Finset.mem_filter, Finset.mem_range, hbound, true_and]
  calc
    _ = ((K.filter fun U =>
        a * n < |((U ∩ T).card : ℝ) - (S.card : ℝ) * T.card / n|).card : ℝ) /
          (K.card : ℝ) := ProductPermutationSubsetLaw F i S _
    _ = ∑ x ∈ E, ((K.filter fun U => (U ∩ T).card = x).card : ℝ) / (K.card : ℝ) := by
      rw [hcount, Nat.cast_sum, Finset.sum_div]
    _ = ∑ x ∈ E, HypergeometricMass n S.card T.card x := by
      apply Finset.sum_congr rfl
      intro x _
      have h := UniformSubsetIntersectionLaw (Finset.univ : Finset (F i)) T
        (Finset.subset_univ _) S.card (by simpa only [Finset.card_univ, hcard] using hS) x
      simpa only [Finset.card_univ, hcard] using h
    _ ≤ _ := HypergeometricTwoTail n S.card T.card hn hS hT a ha
