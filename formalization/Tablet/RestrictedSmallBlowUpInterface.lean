import Tablet.InstanceLowerRegular
import Tablet.CandidacySystem
import Tablet.PartialEmbedding

-- [TABLET NODE: RestrictedSmallBlowUpInterface]
theorem RestrictedSmallBlowUpInterface {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (S : Finset VH) (Δ n : ℕ) (ε d : ENNReal)
    (hreg : InstanceLowerRegular B ε d)
    (hH : H.maxDegree ≤ Δ) (hR : R.maxDegree ≤ Δ)
    (hsmall : ∀ i, ((S.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤
      ε * Fintype.card {v : VG // B.hostCluster v = i})
    (hsize : ∀ i, (1 - ε) * n ≤
        Fintype.card {v : VG // B.hostCluster v = i} ∧
      (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤ (1 + ε) * n)
    (hdeg : ∀ x ∈ S, d * n ≤ Set.ncard {v : VG | A.allowed x v}) :
    ∃ (Bs : BlowUpInstance r {x // x ∈ S} VG (H.induce (S : Set VH)) G R)
      (As : CandidacySystem Bs),
      (∀ x : {x // x ∈ S}, Bs.sourceCluster x = B.sourceCluster x.1) ∧
      (∀ v, Bs.hostCluster v = B.hostCluster v) ∧
      (∀ (x : {x // x ∈ S}) v, As.allowed x v ↔ A.allowed x.1 v) ∧
      (Set.range (fun x : {x // x ∈ S} => x.1) = (S : Set VH)) ∧
      InstanceLowerRegular Bs ε d ∧
      (H.induce (S : Set VH)).maxDegree ≤ Δ ∧ R.maxDegree ≤ Δ ∧
      (∀ i, (Fintype.card {x : {x // x ∈ S} // Bs.sourceCluster x = i} : ENNReal) ≤
        ε * Fintype.card {v : VG // Bs.hostCluster v = i}) ∧
      (∀ i, (1 - ε) * n ≤ Fintype.card {v : VG // Bs.hostCluster v = i} ∧
        (Fintype.card {v : VG // Bs.hostCluster v = i} : ENNReal) ≤ (1 + ε) * n) ∧
      (∀ x, d * n ≤ Set.ncard {v : VG | As.allowed x v}) := by
-- BODY
  classical
  let Bs : BlowUpInstance r {x // x ∈ S} VG (H.induce (S : Set VH)) G R :=
    { sourceCluster := fun x => B.sourceCluster x.1
      hostCluster := B.hostCluster
      source_independent := by
        intro i x hx y hy hxy
        exact B.source_independent i hx hy
          (fun h => hxy (Subtype.ext h))
      capacity := by
        intro i
        let f : {x : {x // x ∈ S} // B.sourceCluster x.1 = i} →
            {x : VH // B.sourceCluster x = i} := fun x => ⟨x.1.1, x.2⟩
        have hf : Function.Injective f := by
          intro x y h
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun t : {x : VH // B.sourceCluster x = i} => t.1) h
        exact (Fintype.card_le_of_injective f hf).trans (B.capacity i)
      reduced_support := fun h => B.reduced_support h }
  let As : CandidacySystem Bs :=
    { allowed := fun x v => A.allowed x.1 v
      cluster_respecting := fun h => A.cluster_respecting h }
  refine ⟨Bs, As, ?_, ?_, ?_, ?_, ?_, ?_, hR, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro v
    rfl
  · intro x v
    rfl
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · change InstanceLowerRegular B ε d
    exact hreg
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro x
    have hd : (H.induce (S : Set VH)).degree x ≤ H.degree x.1 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        ← SimpleGraph.card_neighborSet_eq_degree]
      let f : (H.induce (S : Set VH)).neighborSet x → H.neighborSet x.1 :=
        fun y => ⟨y.1.1, y.2⟩
      apply Fintype.card_le_of_injective f
      intro y z h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : H.neighborSet x.1 => t.1) h
    exact hd.trans ((H.degree_le_maxDegree x.1).trans hH)
  · intro i
    let e : {x : {x // x ∈ S} // Bs.sourceCluster x = i} ≃
        ↥(S.filter fun x => B.sourceCluster x = i) :=
      { toFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun x =>
          ⟨⟨x.1, (Finset.mem_filter.mp x.2).1⟩, (Finset.mem_filter.mp x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    have hc : Fintype.card {x : {x // x ∈ S} // Bs.sourceCluster x = i} =
        (S.filter fun x => B.sourceCluster x = i).card :=
      (Fintype.card_congr e).trans (Fintype.card_coe _)
    rw [hc]
    exact hsmall i
  · exact hsize
  · intro x
    exact hdeg x.1 x.2
