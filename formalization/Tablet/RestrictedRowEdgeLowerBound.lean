import Tablet.FilteredProductRowCount

-- [TABLET NODE: RestrictedRowEdgeLowerBound]
theorem RestrictedRowEdgeLowerBound {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (W B : Finset Y) (P : X → Y → Prop) [DecidableRel P]
    (D : ℝ) (hBW : B ⊆ W)
    (hdegree : ∀ x ∈ A, D ≤ ((W.filter fun y => P x y).card : ℝ)) :
    (A.card : ℝ) * (D - ((W.card : ℝ) - B.card)) ≤
      (((A.product B).filter fun p => P p.1 p.2).card : ℝ) := by
-- BODY
  classical
  have hrow : ∀ x ∈ A,
      D - ((W.card : ℝ) - B.card) ≤ ((B.filter fun y => P x y).card : ℝ) := by
    intro x hx
    have hpartition : W.filter (fun y => P x y) =
        (B.filter fun y => P x y) ∪ ((W \ B).filter fun y => P x y) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hy
        by_cases hb : y ∈ B
        · exact Or.inl ⟨hb, hy.2⟩
        · exact Or.inr ⟨⟨hy.1, hb⟩, hy.2⟩
      · rintro (hy | hy)
        · exact ⟨hBW hy.1, hy.2⟩
        · exact ⟨hy.1.1, hy.2⟩
    have hdisj : Disjoint (B.filter fun y => P x y)
        ((W \ B).filter fun y => P x y) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
        (Finset.mem_filter.mp hy).1
    have hcount := congrArg (fun S : Finset Y => (S.card : ℝ)) hpartition
    dsimp only at hcount
    rw [Finset.card_union_of_disjoint hdisj, Nat.cast_add] at hcount
    have hloss : (((W \ B).filter fun y => P x y).card : ℝ) ≤
        (W.card : ℝ) - B.card := by
      have h := Finset.card_filter_le (W \ B) (fun y => P x y)
      rw [Finset.card_sdiff_of_subset hBW] at h
      have h' : (((W \ B).filter fun y => P x y).card : ℝ) ≤
          ((W.card - B.card : ℕ) : ℝ) := by exact_mod_cast h
      simpa only [Nat.cast_sub (Finset.card_le_card hBW)] using h'
    have hd := hdegree x hx
    linarith
  rw [FilteredProductRowCount A B P, Nat.cast_sum]
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hrow
