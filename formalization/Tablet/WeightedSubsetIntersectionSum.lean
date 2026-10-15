import Tablet.Preamble
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

-- [TABLET NODE: WeightedSubsetIntersectionSum]
theorem WeightedSubsetIntersectionSum (n s : ℕ) (hs : s ≤ n)
    (M : Finset (Fin n)) (r : ℝ) :
    (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      ∏ i ∈ A, if i ∈ M then r else 1) =
    ∑ x ∈ Finset.range (n + 1),
      if x ≤ s then
        ((M.card.choose x : ℝ) * ((n - M.card).choose (s - x) : ℝ)) * r ^ x
      else 0 := by
-- BODY
  classical
  let U : Finset (Fin n) := Finset.univ
  let S := U.powersetCard s
  let F (x : ℕ) := S.filter (fun A => (A ∩ M).card = x)
  have hU : U.card = n := by simp [U]
  have hcomp : (U \ M).card = n - M.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ M), hU]
  have hprod (A : Finset (Fin n)) :
      (∏ i ∈ A, if i ∈ M then r else 1) = r ^ (A ∩ M).card := by
    rw [← Finset.prod_filter]
    have : A.filter (fun i => i ∈ M) = A ∩ M := by ext; simp
    rw [this, Finset.prod_const]
  have hcount (x : ℕ) (hx : x ≤ s) :
      (F x).card = M.card.choose x * (n - M.card).choose (s - x) := by
    let T := M.powersetCard x ×ˢ (U \ M).powersetCard (s - x)
    have hbij : (F x).card = T.card := by
      apply Finset.card_bij (fun A _ => (A ∩ M, A \ M))
      · intro A hA
        obtain ⟨hAS, hAx⟩ := Finset.mem_filter.mp hA
        have hAc : A.card = s := (Finset.mem_powersetCard.mp hAS).2
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hAx⟩
        · apply Finset.mem_powersetCard.mpr
          constructor
          · intro i hi
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
          · rw [Finset.card_sdiff, Finset.inter_comm, hAx, hAc]
      · intro A hA B hB hAB
        have h1 : A ∩ M = B ∩ M := congrArg Prod.fst hAB
        have h2 : A \ M = B \ M := congrArg Prod.snd hAB
        have hAeq : (A ∩ M) ∪ (A \ M) = A := by ext; simp; tauto
        have hBeq : (B ∩ M) ∪ (B \ M) = B := by ext; simp; tauto
        rw [← hAeq, ← hBeq, h1, h2]
      · intro B hB
        obtain ⟨hBM, hBC⟩ := Finset.mem_product.mp hB
        obtain ⟨hBMsub, hBMcard⟩ := Finset.mem_powersetCard.mp hBM
        obtain ⟨hBCsub, hBCcard⟩ := Finset.mem_powersetCard.mp hBC
        have hd : Disjoint B.1 B.2 := by
          apply Finset.disjoint_left.mpr
          intro i hi hj
          exact (Finset.mem_sdiff.mp (hBCsub hj)).2 (hBMsub hi)
        have hi : (B.1 ∪ B.2) ∩ M = B.1 := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hi | hi, hm⟩
            · exact hi
            · exact False.elim ((Finset.mem_sdiff.mp (hBCsub hi)).2 hm)
          · intro hi
            exact ⟨Or.inl hi, hBMsub hi⟩
        have hc : (B.1 ∪ B.2) \ M = B.2 := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hi | hi, hm⟩
            · exact False.elim (hm (hBMsub hi))
            · exact hi
          · intro hi
            exact ⟨Or.inr hi, (Finset.mem_sdiff.mp (hBCsub hi)).2⟩
        refine ⟨B.1 ∪ B.2, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_powersetCard.mpr
            refine ⟨Finset.subset_univ _, ?_⟩
            rw [Finset.card_union_of_disjoint hd, hBMcard, hBCcard]
            omega
          · rw [hi, hBMcard]
        · exact Prod.ext hi hc
    rw [hbij, Finset.card_product, Finset.card_powersetCard,
      Finset.card_powersetCard, hcomp]
  have hsum :
      (∑ x ∈ Finset.range (n + 1), ∑ A ∈ F x,
        ∏ i ∈ A, if i ∈ M then r else 1) =
      ∑ A ∈ S, ∏ i ∈ A, if i ∈ M then r else 1 := by
    apply Finset.sum_fiberwise_of_maps_to
    intro A hA
    apply Finset.mem_range.mpr
    have hAc : A.card = s := (Finset.mem_powersetCard.mp hA).2
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := M))
    omega
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxs : x ≤ s
  · rw [if_pos hxs]
    calc
      _ = ∑ _A ∈ F x, r ^ x := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [hprod, (Finset.mem_filter.mp hA).2]
      _ = _ := by simp [hcount x hxs, Nat.cast_mul]
  · rw [if_neg hxs]
    apply Finset.sum_eq_zero
    intro A hA
    obtain ⟨hAS, hAx⟩ := Finset.mem_filter.mp hA
    have hAc : A.card = s := (Finset.mem_powersetCard.mp hAS).2
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := M))
    omega
