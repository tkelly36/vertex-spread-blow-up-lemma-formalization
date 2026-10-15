import Tablet.CandidacySuperRegular
import Tablet.SuperRegularPairEmbedding

open scoped Classical

-- [TABLET NODE: TaggedCandidacyAssembly]
theorem TaggedCandidacyAssembly {r s : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H H' : SimpleGraph VH} {G G' : SimpleGraph VG}
    {R : SimpleGraph (Fin r)} {R' : SimpleGraph (Fin s)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (B' : BlowUpInstance s VH VG H' G' R') (η c : ENNReal)
    (hpair : ∀ j : Fin s,
      let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ x, z = Sum.inl x ∧ B'.sourceCluster x = j
      let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ v, z = Sum.inr v ∧ B'.hostCluster v = j
      let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
        ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A.allowed x v
      ∃ F : SimpleGraph (VH ⊕ VG), ∃ _ : DecidableRel F.Adj,
        F ≤ C ∧ SuperRegularPair F L Q η c) :
    ∃ A' : CandidacySystem B',
      (∀ ⦃x v⦄, A'.allowed x v → A.allowed x v) ∧
      CandidacySuperRegular B' A' η c := by
-- BODY
  classical
  choose F hFdec hFle hFreg using hpair
  let A' : CandidacySystem B' := {
    allowed := fun x v => B'.sourceCluster x = B'.hostCluster v ∧
      (F (B'.sourceCluster x)).Adj (Sum.inl x) (Sum.inr v)
    cluster_respecting := fun h => h.1 }
  refine ⟨A', ?_, ?_⟩
  · intro x v h
    have hc := hFle (B'.sourceCluster x) h.2
    simpa [SimpleGraph.fromRel_adj] using hc
  intro j
  let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
    ∃ x, z = Sum.inl x ∧ B'.sourceCluster x = j
  let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
    ∃ v, z = Sum.inr v ∧ B'.hostCluster v = j
  let C' : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
    ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A'.allowed x v
  letI : DecidableRel C'.Adj := Classical.decRel _
  change SuperRegularPair C' L Q η c
  letI : DecidableRel (F j).Adj := hFdec j
  have hcross : ∀ z ∈ L, ∀ w ∈ Q, C'.Adj z w ↔ (F j).Adj z w := by
    intro z hz w hw
    obtain ⟨x, rfl, hx⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hw).2
    have hA : A'.allowed x v ↔ (F j).Adj (Sum.inl x) (Sum.inr v) := by
      change (B'.sourceCluster x = B'.hostCluster v ∧
        (F (B'.sourceCluster x)).Adj (Sum.inl x) (Sum.inr v)) ↔ _
      simp only [hx, hv, true_and]
    simpa [C', SimpleGraph.fromRel_adj] using hA
  simpa only [Finset.image_id] using
    SuperRegularPairEmbedding id Function.injective_id (F j) C' L Q η c
      hcross (hFreg j)
