import Tablet.InstanceLowerSuperRegular
import Tablet.CandidacyLowerSuperRegular
import Tablet.InstanceLowerRegular

-- [TABLET NODE: RebalancingRestrictionEstimates]
theorem RebalancingRestrictionEstimates {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel G.Adj]
    {R : SimpleGraph (Fin r)} (B : BlowUpInstance r VH VG H G R)
    (A : CandidacySystem B) (n : ℕ) (ε d a : ENNReal)
    (hεa : ε ≤ a)
    (hhost : InstanceLowerSuperRegular B ε d)
    (hcand : CandidacyLowerSuperRegular B A ε d)
    (hsize : ∀ i, (1 - ε) * n ≤ Fintype.card {v : VG // B.hostCluster v = i} ∧
      (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤ (1 + ε) * n)
    (hdegree : ∀ i, (d / 2) * n ≤
      (d - ε) * Fintype.card {v : VG // B.hostCluster v = i}) :
    InstanceLowerRegular B a (d / 2) ∧
    (∀ i, (1 - a) * n ≤ Fintype.card {v : VG // B.hostCluster v = i} ∧
      (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤ (1 + a) * n) ∧
    (∀ x, (d / 2) * n ≤ Set.ncard {v : VG | A.allowed x v}) := by
-- BODY
  classical
  have hhalf : d / 2 ≤ d := by
    simpa using ENNReal.div_le_div_left (show (1 : ENNReal) ≤ 2 by norm_num) d
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij U hU W hW hUt hWt
    exact (tsub_le_tsub hhalf hεa).trans
      ((hhost hij).1 U hU W hW
        ((mul_le_mul_left hεa _).trans_lt hUt)
        ((mul_le_mul_left hεa _).trans_lt hWt))
  · intro i
    exact ⟨(mul_le_mul_left (tsub_le_tsub_left hεa 1) _).trans (hsize i).1,
      (hsize i).2.trans (mul_le_mul_left (add_le_add_right hεa 1) _)⟩
  · intro x
    let i := B.sourceCluster x
    let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = i
    let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = i
    let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
      ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ q = Sum.inr v ∧ A.allowed y v
    letI : DecidableRel C.Adj := Classical.decRel _
    have hleft : Sum.inl x ∈ L := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨x, rfl, rfl⟩
    have hadj (v : VG) : C.Adj (Sum.inl x) (Sum.inr v) ↔ A.allowed x v := by
      simp [C, SimpleGraph.fromRel_adj]
    have hQ : Q.card = Fintype.card {v : VG // B.hostCluster v = i} := by
      rw [Fintype.card_subtype]
      symm
      apply Finset.card_bij (fun v _ => Sum.inr v)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, rfl, hv⟩
      · intro v hv w hw heq
        exact Sum.inr_injective heq
      · intro z hz
        obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hz).2
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    have hneighbors : (Q.filter fun z => C.Adj (Sum.inl x) z).card =
        Set.ncard {v : VG | A.allowed x v} := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      symm
      apply Finset.card_bij (fun v _ => Sum.inr v)
      · intro v hv
        have hav : A.allowed x v := (Finset.mem_filter.mp hv).2
        apply Finset.mem_filter.mpr
        refine ⟨?_, (hadj v).mpr hav⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, v, rfl, (A.cluster_respecting hav).symm⟩
      · intro v hv w hw heq
        exact Sum.inr_injective heq
      · intro z hz
        obtain ⟨hzQ, hzadj⟩ := Finset.mem_filter.mp hz
        obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hzQ).2
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hadj v).mp hzadj⟩, rfl⟩
    have hdeg := (hcand i).2.1 (Sum.inl x) hleft
    change (d - ε) * (Q.card : ENNReal) ≤
      ((Q.filter fun z => C.Adj (Sum.inl x) z).card : ENNReal) at hdeg
    rw [hQ, hneighbors] at hdeg
    exact (hdegree i).trans hdeg
