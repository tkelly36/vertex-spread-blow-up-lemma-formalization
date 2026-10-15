import Tablet.BlowUpInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- [TABLET NODE: ClusterwiseDeletionBuffer]
theorem ClusterwiseDeletionBuffer {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] {H : SimpleGraph VH} {G : SimpleGraph VG}
    {R : SimpleGraph (Fin r)} (B : BlowUpInstance r VH VG H G R)
    (m k Δ : ℕ) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hEq : ∀ i, Fintype.card {x : VH // B.sourceCluster x = i} =
      Fintype.card {v : VG // B.hostCluster v = i})
    (hm : ∀ i, m ≤ Fintype.card {v : VG // B.hostCluster v = i})
    (hk : ∀ i, Fintype.card {v : VG // B.hostCluster v = i} - m ≤ k)
    (hH : H.maxDegree ≤ Δ) (hR : R.maxDegree ≤ Δ) :
    ∃ X : Finset VH,
      (∀ i, (X.filter fun x => B.sourceCluster x = i).card =
        Fintype.card {v : VG // B.hostCluster v = i} - m) ∧
      (∀ i, (X.filter fun x => B.sourceCluster x = i).card ≤ k) ∧
      let X' := Finset.univ.filter fun x => x ∉ X ∧ ∃ y ∈ X, H.Adj x y
      ∀ i, (X'.filter fun x => B.sourceCluster x = i).card ≤ Δ * Δ * k := by
-- BODY
  classical
  have hchoose : ∀ i : Fin r, ∃ S : Finset VH,
      S ⊆ Finset.univ.filter (fun x => B.sourceCluster x = i) ∧
      S.card = Fintype.card {v : VG // B.hostCluster v = i} - m := by
    intro i
    apply Finset.exists_subset_card_eq
    rw [← Fintype.card_subtype, hEq i]
    exact Nat.sub_le _ _
  choose S hSsub hScard using hchoose
  let X := Finset.univ.biUnion S
  have hScluster : ∀ i x, x ∈ S i → B.sourceCluster x = i := by
    intro i x hx
    exact (Finset.mem_filter.mp (hSsub i hx)).2
  have hfilter : ∀ i, X.filter (fun x => B.sourceCluster x = i) = S i := by
    intro i
    ext x
    constructor
    · intro hx
      obtain ⟨hxX, hxi⟩ := Finset.mem_filter.mp hx
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hxX
      have hji : j = i := (hScluster j x hxj).symm.trans hxi
      simpa only [hji] using hxj
    · intro hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩, hScluster i x hx⟩
  have hXcard : ∀ i, (X.filter (fun x => B.sourceCluster x = i)).card ≤ k := by
    intro i
    rw [hfilter i, hScard i]
    exact hk i
  refine ⟨X, ?_, hXcard, ?_⟩
  · intro i
    rw [hfilter i, hScard i]
  · dsimp only
    intro i
    let Y := (R.neighborFinset i).biUnion
      (fun j => X.filter (fun y => B.sourceCluster y = j))
    have hYcard : Y.card ≤ Δ * k := by
      calc
        Y.card ≤ (R.neighborFinset i).card * k :=
          Finset.card_biUnion_le_card_mul _ _ _ (fun j _ => hXcard j)
        _ ≤ Δ * k := Nat.mul_le_mul_right k
          ((R.card_neighborFinset_eq_degree i).le.trans
            ((R.degree_le_maxDegree i).trans hR))
    have hbuffer :
        ((Finset.univ.filter fun x => x ∉ X ∧ ∃ y ∈ X, H.Adj x y).filter
          fun x => B.sourceCluster x = i) ⊆ Y.biUnion (fun y => H.neighborFinset y) := by
      intro x hx
      obtain ⟨hxbuf, hxi⟩ := Finset.mem_filter.mp hx
      obtain ⟨y, hyX, hxy⟩ := (Finset.mem_filter.mp hxbuf).2.2
      have hij : R.Adj i (B.sourceCluster y) := by
        simpa only [hxi] using B.reduced_support hxy
      have hyY : y ∈ Y := Finset.mem_biUnion.mpr
        ⟨B.sourceCluster y, (R.mem_neighborFinset i _).mpr hij,
          Finset.mem_filter.mpr ⟨hyX, rfl⟩⟩
      exact Finset.mem_biUnion.mpr
        ⟨y, hyY, (H.mem_neighborFinset y x).mpr (H.adj_symm hxy)⟩
    calc
      _ ≤ (Y.biUnion (fun y => H.neighborFinset y)).card := Finset.card_le_card hbuffer
      _ ≤ Y.card * Δ := Finset.card_biUnion_le_card_mul _ _ _ (fun y _ =>
        (H.card_neighborFinset_eq_degree y).le.trans
          ((H.degree_le_maxDegree y).trans hH))
      _ ≤ (Δ * k) * Δ := Nat.mul_le_mul_right Δ hYcard
      _ = Δ * Δ * k := by ac_rfl
