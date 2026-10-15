import Tablet.GreedyPartialEmbedding
import Tablet.UpdatedCandidacy

-- [TABLET NODE: GreedyPartialEmbeddingReserve]
theorem GreedyPartialEmbeddingReserve (Δ : ℕ) (d ε a d' : ENNReal) (n : ℕ)
    (hpower : ∀ k : ℕ, k ≤ Δ → a ≤ d * (d - ε) ^ k)
    (hloss : ε * (1 + ε) ≤ a / 2) (hd' : d' ≤ a / 2)
    {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel H.Adj]
    {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (hdeg : H.maxDegree ≤ Δ)
    (hsmall : ∀ i, (Fintype.card {x : VH // B.sourceCluster x = i} : ENNReal) ≤
      ε * Fintype.card {v : VG // B.hostCluster v = i})
    (hhost : ∀ i, (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤
      (1 + ε) * n)
    (S : Finset VH) (f : GreedyPartialEmbedding B A d ε n S) :
    ∀ x, x ∉ S → d' * n ≤ Set.ncard
      {v : VG | (UpdatedCandidacy B A S f.toPartialCompatibleEmbedding).allowed x v} := by
-- BODY
  classical
  intro x hx
  let W := RawCandidates B A S f.toFun x
  let O := (S.filter fun y => B.sourceCluster y = B.sourceCluster x).image f.toFun
  have memraw (v : VG) : v ∈ W ↔
      A.allowed x v ∧ ∀ y ∈ S, H.Adj x y → G.Adj v (f.toFun y) := by
    simp [W, RawCandidates]
  have hk : (S.filter fun y => H.Adj x y).card ≤ Δ := by
    apply le_trans _ ((H.degree_le_maxDegree x).trans hdeg)
    change (S.filter fun y => H.Adj x y).card ≤ (H.neighborFinset x).card
    apply Finset.card_le_card
    intro y hy
    exact (H.mem_neighborFinset x y).mpr (Finset.mem_filter.mp hy).2
  have hraw : a * n ≤ (W.card : ENNReal) := by
    calc
      a * n ≤ d * (d - ε) ^ (S.filter fun y => H.Adj x y).card * n := by
        gcongr
        exact hpower _ hk
      _ ≤ (W.card : ENNReal) := f.raw_bound x hx
  have hOcard : O.card ≤ Fintype.card {y : VH // B.sourceCluster y = B.sourceCluster x} := by
    apply (Finset.card_image_le).trans
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hO : (O.card : ENNReal) ≤ a / 2 * n := by
    calc
      (O.card : ENNReal) ≤ Fintype.card {y : VH // B.sourceCluster y = B.sourceCluster x} :=
        by exact_mod_cast hOcard
      _ ≤ ε * Fintype.card {v : VG // B.hostCluster v = B.sourceCluster x} := hsmall _
      _ ≤ ε * ((1 + ε) * n) := by gcongr; exact hhost _
      _ = (ε * (1 + ε)) * n := (mul_assoc _ _ _).symm
      _ ≤ a / 2 * n := by gcongr
  have havail : {v : VG | (UpdatedCandidacy B A S f.toPartialCompatibleEmbedding).allowed x v} =
      (↑(W \ O) : Set VG) := by
    ext v
    change (x ∉ S ∧ v ∉ S.image f.toFun ∧ A.allowed x v ∧
        ∀ y ∈ S, H.Adj x y → G.Adj v (f.toFun y)) ↔ v ∈ W \ O
    constructor
    · rintro ⟨_, hv, ha, he⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨(memraw v).mpr ⟨ha, he⟩, ?_⟩
      intro hvo
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hvo
      exact hv (Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, hyv⟩)
    · intro hv
      obtain ⟨hW, hO'⟩ := Finset.mem_sdiff.mp hv
      have hW' : A.allowed x v ∧ ∀ y ∈ S, H.Adj x y → G.Adj v (f.toFun y) :=
        (memraw v).mp hW
      refine ⟨hx, ?_, hW'⟩
      intro hvs
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hvs
      have hycluster : B.sourceCluster y = B.sourceCluster x := by
        calc
          B.sourceCluster y = B.hostCluster (f.toFun y) :=
            A.cluster_respecting (f.compatible y hy)
          _ = B.hostCluster v := congrArg B.hostCluster hyv
          _ = B.sourceCluster x := (A.cluster_respecting hW'.1).symm
      exact hO' (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hycluster⟩, hyv⟩)
  rw [havail, Set.ncard_coe_finset]
  have hcount : (W.card : ENNReal) ≤ ((W \ O).card : ENNReal) + O.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := W) (t := O))
  have hhalf : a / 2 * n ≤ (W.card : ENNReal) := by
    calc
      a / 2 * n ≤ a * n := by gcongr; exact ENNReal.half_le_self
      _ ≤ (W.card : ENNReal) := hraw
  have hhalftop : a / 2 * n ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhalf
  have hsum : a / 2 * n + a / 2 * n ≤ ((W \ O).card : ENNReal) + a / 2 * n := by
    calc
      a / 2 * n + a / 2 * n = a * n := by rw [← add_mul, ENNReal.add_halves]
      _ ≤ (W.card : ENNReal) := hraw
      _ ≤ ((W \ O).card : ENNReal) + O.card := hcount
      _ ≤ ((W \ O).card : ENNReal) + a / 2 * n := by gcongr
  calc
    d' * n ≤ a / 2 * n := by gcongr
    _ ≤ ((W \ O).card : ENNReal) := ENNReal.le_of_add_le_add_right hhalftop hsum
