import Tablet.UpdatedCandidacy

-- [TABLET NODE: RebalancingResidualGeometry]
theorem RebalancingResidualGeometry {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X : Finset VH) (f : PartialCompatibleEmbedding B A X) (m : ℕ)
    (hEq : ∀ i, Fintype.card {x : VH // B.sourceCluster x = i} =
      Fintype.card {v : VG // B.hostCluster v = i})
    (hm : ∀ i, m ≤ Fintype.card {v : VG // B.hostCluster v = i})
    (hX : ∀ i, (X.filter fun x => B.sourceCluster x = i).card =
      Fintype.card {v : VG // B.hostCluster v = i} - m) :
    let Y := {x : VH // x ∉ X}
    let W := {v : VG // v ∉ X.image f.toFun}
    ∃ Br : BlowUpInstance r Y W (H.induce {x : VH | x ∉ X})
        (G.induce {v : VG | v ∉ X.image f.toFun}) R,
    ∃ Ar : CandidacySystem Br,
      (∀ x : Y, Br.sourceCluster x = B.sourceCluster x.1) ∧
      (∀ v : W, Br.hostCluster v = B.hostCluster v.1) ∧
      (∀ (x : Y) (v : W), Ar.allowed x v ↔
        (UpdatedCandidacy B A X f).allowed x.1 v.1) ∧
      (∀ i, Fintype.card {x : Y // Br.sourceCluster x = i} = m) ∧
      (∀ i, Fintype.card {v : W // Br.hostCluster v = i} = m) ∧
      (∀ i, ((X.image f.toFun).filter fun v => B.hostCluster v = i).card =
        (X.filter fun x => B.sourceCluster x = i).card) := by
-- BODY
  classical
  have hcluster (x : VH) (hx : x ∈ X) :
      B.sourceCluster x = B.hostCluster (f.toFun x) :=
    A.cluster_respecting (f.compatible x hx)
  have himage (i : Fin r) :
      (X.image f.toFun).filter (fun v => B.hostCluster v = i) =
        (X.filter fun x => B.sourceCluster x = i).image f.toFun := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hi⟩
      exact ⟨x, ⟨hx, (hcluster x hx).trans hi⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (hcluster x hx).symm.trans hi⟩
  have hremoved (i : Fin r) :
      ((X.image f.toFun).filter fun v => B.hostCluster v = i).card =
        (X.filter fun x => B.sourceCluster x = i).card := by
    rw [himage]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    exact f.injOn (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  have hsource (i : Fin r) :
      Fintype.card {x : {x : VH // x ∉ X} // B.sourceCluster x.1 = i} = m := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun x => B.sourceCluster x = i) (fun x : VH => x ∈ X)
    have ha : ((Finset.univ.filter fun x => B.sourceCluster x = i).filter
        fun x => x ∈ X) = X.filter (fun x => B.sourceCluster x = i) := by
      ext x
      simp [and_comm]
    rw [ha, hX, ← Fintype.card_subtype, hEq] at hpart
    have hb : Fintype.card {x : {x : VH // x ∉ X} // B.sourceCluster x.1 = i} =
        ((Finset.univ.filter fun x => B.sourceCluster x = i).filter
          fun x => x ∉ X).card := by
      let e : {x : {x : VH // x ∉ X} // B.sourceCluster x.1 = i} ≃
          ↥((Finset.univ.filter fun x => B.sourceCluster x = i).filter fun x => x ∉ X) :=
        { toFun := fun x => ⟨x.1.1, Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩, x.1.2⟩⟩
          invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.mp x.2).2⟩,
            (Finset.mem_filter.mp (Finset.mem_filter.mp x.2).1).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_coe _)
    rw [hb]
    have := hm i
    omega
  have hhost (i : Fin r) :
      Fintype.card {v : {v : VG // v ∉ X.image f.toFun} //
        B.hostCluster v.1 = i} = m := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun v => B.hostCluster v = i)
      (fun v : VG => v ∈ X.image f.toFun)
    have ha : ((Finset.univ.filter fun v => B.hostCluster v = i).filter
        fun v => v ∈ X.image f.toFun) =
        (X.image f.toFun).filter (fun v => B.hostCluster v = i) := by
      ext v
      simp [and_comm]
    rw [ha, hremoved, hX, ← Fintype.card_subtype] at hpart
    have hb : Fintype.card {v : {v : VG // v ∉ X.image f.toFun} //
        B.hostCluster v.1 = i} =
        ((Finset.univ.filter fun v => B.hostCluster v = i).filter
          fun v => v ∉ X.image f.toFun).card := by
      let e : {v : {v : VG // v ∉ X.image f.toFun} // B.hostCluster v.1 = i} ≃
          ↥((Finset.univ.filter fun v => B.hostCluster v = i).filter
            fun v => v ∉ X.image f.toFun) :=
        { toFun := fun v => ⟨v.1.1, Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.2⟩, v.1.2⟩⟩
          invFun := fun v => ⟨⟨v.1, (Finset.mem_filter.mp v.2).2⟩,
            (Finset.mem_filter.mp (Finset.mem_filter.mp v.2).1).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_coe _)
    rw [hb]
    have := hm i
    omega
  let Br : BlowUpInstance r {x : VH // x ∉ X} {v : VG // v ∉ X.image f.toFun}
      (H.induce {x : VH | x ∉ X}) (G.induce {v : VG | v ∉ X.image f.toFun}) R :=
    { sourceCluster := fun x => B.sourceCluster x.1
      hostCluster := fun v => B.hostCluster v.1
      source_independent := by
        intro i x hx y hy hxy
        exact B.source_independent i hx hy (fun h => hxy (Subtype.ext h))
      capacity := by
        intro i
        change Fintype.card {x : {x : VH // x ∉ X} // B.sourceCluster x.1 = i} ≤
          Fintype.card {v : {v : VG // v ∉ X.image f.toFun} // B.hostCluster v.1 = i}
        rw [hsource i, hhost i]
      reduced_support := fun h => B.reduced_support h }
  let Ar : CandidacySystem Br :=
    { allowed := fun x v => (UpdatedCandidacy B A X f).allowed x.1 v.1
      cluster_respecting := fun h => (UpdatedCandidacy B A X f).cluster_respecting h }
  exact ⟨Br, Ar, (fun _ => rfl), (fun _ => rfl), (fun _ _ => Iff.rfl),
    hsource, hhost, hremoved⟩
