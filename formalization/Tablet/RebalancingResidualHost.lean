import Tablet.InstanceLowerSuperRegular
import Tablet.PartialCompatibleEmbedding
import Tablet.LowerSuperRegularDeletionSlicing
import Tablet.LowerSuperRegularPairEmbedding

-- [TABLET NODE: RebalancingResidualHost]
theorem RebalancingResidualHost {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel G.Adj]
    {R : SimpleGraph (Fin r)} (B : BlowUpInstance r VH VG H G R)
    (A : CandidacySystem B) (X : Finset VH) (f : PartialCompatibleEmbedding B A X)
    (Br : BlowUpInstance r {x : VH // x ∉ X} {v : VG // v ∉ X.image f.toFun}
      (H.induce {x : VH | x ∉ X}) (G.induce {v : VG | v ∉ X.image f.toFun}) R)
    (m : ℕ) (ε d ε' d' L : ENNReal)
    (hmap : ∀ v, Br.hostCluster v = B.hostCluster v.1)
    (hcard : ∀ i, Fintype.card {v : {v : VG // v ∉ X.image f.toFun} //
      Br.hostCluster v = i} = m)
    (hSR : InstanceLowerSuperRegular B ε d)
    (hremoved : ∀ i, (((X.image f.toFun).filter fun v => B.hostCluster v = i).card :
      ENNReal) ≤ L)
    (hthreshold : ∀ i, ε * Fintype.card {v : VG // B.hostCluster v = i} ≤ ε' * m)
    (hdensity : d' - ε' ≤ d - ε)
    (hdegree : ∀ i, (d' - ε') * m ≤
      (d - ε) * Fintype.card {v : VG // B.hostCluster v = i} - L) :
    InstanceLowerSuperRegular Br ε' d' := by
-- BODY
  classical
  let S := {v : VG | v ∉ X.image f.toFun}
  let e : S ↪ VG := Function.Embedding.subtype (· ∈ S)
  let U (i : Fin r) : Finset VG := Finset.univ.filter fun v => B.hostCluster v = i
  let D (i : Fin r) : Finset VG :=
    (X.image f.toFun).filter fun v => B.hostCluster v = i
  let T (i : Fin r) : Finset S := Finset.univ.filter fun v => Br.hostCluster v = i
  have hDsub (i : Fin r) : D i ⊆ U i := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  have hpart (i : Fin r) : (T i).map e = U i \ D i := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      have hi : B.hostCluster w.1 = i :=
        (hmap w).symm.trans (Finset.mem_filter.mp hw).2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      intro hwD
      exact w.2 (Finset.mem_filter.mp hwD).1
    · intro hv
      obtain ⟨hvU, hvD⟩ := Finset.mem_sdiff.mp hv
      have hi : B.hostCluster v = i := (Finset.mem_filter.mp hvU).2
      have hvX : v ∉ X.image f.toFun := by
        intro hvX
        exact hvD (Finset.mem_filter.mpr ⟨hvX, hi⟩)
      refine Finset.mem_map.mpr ⟨⟨v, hvX⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmap _).trans hi⟩
  have hTcard (i : Fin r) : (T i).card = m := by
    simpa only [Fintype.card_subtype] using hcard i
  have hUcard (i : Fin r) : (U i).card =
      Fintype.card {v : VG // B.hostCluster v = i} :=
    (Fintype.card_subtype _).symm
  have hdiffcard (i : Fin r) : (U i \ D i).card = m := by
    rw [← hpart i, Finset.card_map, hTcard i]
  intro i j hij
  have hpair : LowerSuperRegularPair G (U i) (U j) ε d := hSR hij
  have hReg : LowerRegularPair G (U i \ D i) (U j \ D j) ε' d' := by
    intro P hP Q hQ hPt hQt
    apply hdensity.trans
    apply hpair.1 P (fun v hv => (Finset.mem_sdiff.mp (hP hv)).1)
      Q (fun v hv => (Finset.mem_sdiff.mp (hQ hv)).1)
    · rw [hdiffcard i] at hPt
      rw [hUcard i]
      exact (hthreshold i).trans_lt hPt
    · rw [hdiffcard j] at hQt
      rw [hUcard j]
      exact (hthreshold j).trans_lt hQt
  have hmargin (i : Fin r) :
      (d' - ε') * ((U i \ D i).card : ENNReal) ≤
        (d - ε) * ((U i).card : ENNReal) - ((D i).card : ENNReal) := by
    rw [hdiffcard i, hUcard i]
    exact (hdegree i).trans (tsub_le_tsub_left (hremoved i) _)
  have hres := LowerSuperRegularDeletionSlicing G (U i) (U j) (D i) (D j)
    ε d ε' d' (hDsub i) (hDsub j) hpair hReg (hmargin j) (hmargin i)
  have hambient : LowerSuperRegularPair G ((T i).map e) ((T j).map e) ε' d' := by
    rw [hpart i, hpart j]
    exact hres
  apply (LowerSuperRegularPairEmbedding (Subtype.val : S → VG)
    Subtype.val_injective (G.induce S) G (T i) (T j) ε' d'
    (fun _ _ _ _ => Iff.rfl)).mpr
  simpa only [Finset.map_eq_image] using hambient
