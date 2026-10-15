import Tablet.UpdatedCandidacyCluster

-- [TABLET NODE: UpdatedCandidacyNonneighborExtension]
theorem UpdatedCandidacyNonneighborExtension
    {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X Y X' : Finset VH) (f : PartialCompatibleEmbedding B A X)
    (h : PartialCompatibleEmbedding B A X') (i j : Fin r)
    (hdom : X' = X ∪ Y) (hY : ∀ y ∈ Y, B.sourceCluster y = i)
    (hun : ∀ y, B.sourceCluster y = j → y ∉ X')
    (hji : ¬R.Adj j i) (hij : j ≠ i)
    (hag : ∀ x ∈ X, h.toFun x = f.toFun x) :
    UpdatedCandidacyCluster B A X' h j = UpdatedCandidacyCluster B A X f j ∧
    (∀ y, B.sourceCluster y = j → (y ∉ X' ↔ y ∉ X)) ∧
    (∀ v, B.hostCluster v = j →
      (v ∉ X'.image h.toFun ↔ v ∉ X.image f.toFun)) := by
-- BODY
  classical
  have hsub : X ⊆ X' := by rw [hdom]; exact Finset.subset_union_left
  have source (y : VH) (hy : B.sourceCluster y = j) : y ∉ X :=
    fun hx => hun y hy (hsub hx)
  have oldHost (v : VG) (hv : B.hostCluster v = j) : v ∉ X.image f.toFun := by
    rintro hm
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hm
    have hc := A.cluster_respecting (f.compatible x hx)
    rw [hfx, hv] at hc
    exact source x hc hx
  have newHost (v : VG) (hv : B.hostCluster v = j) : v ∉ X'.image h.toFun := by
    rintro hm
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hm
    have hc := A.cluster_respecting (h.compatible x hx)
    rw [hfx, hv] at hc
    exact hun x hc hx
  refine ⟨?_, fun y hy => ⟨fun _ => source y hy, fun _ => hun y hy⟩,
    fun v hv => ⟨fun _ => oldHost v hv, fun _ => newHost v hv⟩⟩
  ext p
  change (B.sourceCluster p.1 = j ∧ B.hostCluster p.2 = j ∧
    p.1 ∉ X' ∧ p.2 ∉ X'.image h.toFun ∧ A.allowed p.1 p.2 ∧
      ∀ x ∈ X', H.Adj p.1 x → G.Adj p.2 (h.toFun x)) ↔
    (B.sourceCluster p.1 = j ∧ B.hostCluster p.2 = j ∧
    p.1 ∉ X ∧ p.2 ∉ X.image f.toFun ∧ A.allowed p.1 p.2 ∧
      ∀ x ∈ X, H.Adj p.1 x → G.Adj p.2 (f.toFun x))
  constructor
  · rintro ⟨hs, ht, _, _, ha, hadj⟩
    refine ⟨hs, ht, source p.1 hs, oldHost p.2 ht, ha, ?_⟩
    intro x hx hpx
    simpa only [hag x hx] using hadj x (hsub hx) hpx
  · rintro ⟨hs, ht, _, _, ha, hadj⟩
    refine ⟨hs, ht, hun p.1 hs, newHost p.2 ht, ha, ?_⟩
    intro x hx hpx
    rw [hdom] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa only [hag x hx] using hadj x hx hpx
    · have hr := B.reduced_support hpx
      rw [hs, hY x hx] at hr
      exact (hji hr).elim
