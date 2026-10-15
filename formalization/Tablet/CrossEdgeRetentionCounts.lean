import Tablet.CrossEdgeRetention
import Tablet.IndependentRetentionCount

open scoped Classical

-- [TABLET NODE: CrossEdgeRetentionCounts]
theorem CrossEdgeRetentionCounts {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V)
    (hLR : Disjoint L R) (ω : V × V → Bool) :
    CrossEdgeRetention G L R ω ≤ G ∧
    (∀ (U : Finset V), U ⊆ L → ∀ (W : Finset V), W ⊆ R →
      (((U.product W).filter fun p => (CrossEdgeRetention G L R ω).Adj p.1 p.2).card) =
        IndependentRetentionCount ((U.product W).filter fun p => G.Adj p.1 p.2) ω) ∧
    (∀ v ∈ L,
      (R.filter fun w => (CrossEdgeRetention G L R ω).Adj v w).card =
        IndependentRetentionCount ((({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2) ω) ∧
    (∀ w ∈ R,
      (L.filter fun v => (CrossEdgeRetention G L R ω).Adj v w).card =
        IndependentRetentionCount ((L.product {w}).filter fun p => G.Adj p.1 p.2) ω) := by
-- BODY
  classical
  have ha (v w : V) (hv : v ∈ L) (hw : w ∈ R) :
      (CrossEdgeRetention G L R ω).Adj v w ↔ G.Adj v w ∧ ω (v,w) = true := by
    have hwL : w ∉ L := fun h => Finset.disjoint_left.mp hLR h hw
    simp [CrossEdgeRetention, hv, hw, hwL]
  refine ⟨fun _ _ h => h.1, ?_, ?_, ?_⟩
  · intro U hU W hW
    unfold IndependentRetentionCount
    apply congrArg Finset.card
    ext p
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hpU, hpW⟩, hp⟩
      exact ⟨⟨⟨hpU, hpW⟩, (ha _ _ (hU hpU) (hW hpW)).mp hp |>.1⟩,
        (ha _ _ (hU hpU) (hW hpW)).mp hp |>.2⟩
    · rintro ⟨⟨⟨hpU, hpW⟩, hpG⟩, hpω⟩
      exact ⟨⟨hpU, hpW⟩, (ha _ _ (hU hpU) (hW hpW)).mpr ⟨hpG, hpω⟩⟩
  · intro v hv
    unfold IndependentRetentionCount
    rw [Finset.filter_filter]
    have he : ((({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2 ∧ ω p = true) =
        ({v} : Finset V).product (R.filter fun w => (CrossEdgeRetention G L R ω).Adj v w) := by
      ext p
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨rfl, hw⟩, hp⟩
        exact ⟨rfl, hw, (ha _ _ hv hw).mpr hp⟩
      · rintro ⟨rfl, hw, hp⟩
        exact ⟨⟨rfl, hw⟩, (ha _ _ hv hw).mp hp⟩
    rw [he]
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, one_mul]
  · intro w hw
    unfold IndependentRetentionCount
    rw [Finset.filter_filter]
    have he : ((L.product {w}).filter fun p => G.Adj p.1 p.2 ∧ ω p = true) =
        (L.filter fun v => (CrossEdgeRetention G L R ω).Adj v w).product {w} := by
      ext p
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hv, rfl⟩, hp⟩
        exact ⟨⟨hv, (ha _ _ hv hw).mpr hp⟩, rfl⟩
      · rintro ⟨⟨hv, hp⟩, rfl⟩
        exact ⟨⟨hv, rfl⟩, (ha _ _ hv hw).mp hp⟩
    rw [he]
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, mul_one]
