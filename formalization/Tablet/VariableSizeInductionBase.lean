import Tablet.ColourRoundInvariant
import Tablet.CandidacySuperRegular

-- [TABLET NODE: VariableSizeInductionBase]
theorem VariableSizeInductionBase
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (epsilon density : ℕ → ENNReal)
    (D : ℕ) (d C : ENNReal) (n : ℕ)
    (hq : 0 < q) (hdensity : density 0 = d) (hC : C / n ≤ 1)
    (hdegree : ∀ j : Fin r,
      (Finset.univ.filter fun k : Fin r => R.Adj j k).card ≤ D)
    (hcolour : ∀ ⦃i j : Fin r⦄, i ≠ j →
      (R.Adj i j ∨ ∃ k : Fin r, R.Adj i k ∧ R.Adj k j) →
      colour i ≠ colour j)
    (hA : CandidacySuperRegular B A (epsilon 0) d) :
    ∃ μ : PMF (PartialCompatibleEmbedding B A ∅),
      ColourRoundInvariant B A colour epsilon density D C n 0 ∅ ∅ μ := by
-- BODY
  classical
  have host_nonempty (x : VH) : Nonempty {v : VG // B.hostCluster v = B.sourceCluster x} := by
    have hs : 0 < Fintype.card {y : VH // B.sourceCluster y = B.sourceCluster x} :=
      Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    exact Fintype.card_pos_iff.mp (lt_of_lt_of_le hs (B.capacity (B.sourceCluster x)))
  let f0 : PartialCompatibleEmbedding B A ∅ :=
    { toFun := fun x => (Classical.choice (host_nonempty x)).val
      injOn := by intro x hx; simp at hx
      map_adj := by intro x y hx; simp at hx
      compatible := by intro x hx; simp at hx }
  let μ := PMF.pure f0
  refine ⟨μ, hq, hdegree, hcolour, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp at hj
  · simp
  · refine ⟨hC, ?_⟩
    intro s x y hx hy
    cases s with
    | zero =>
      have hc : CylinderEvent x y = Set.univ := by
        ext f
        simp [CylinderEvent]
      rw [hc, pow_zero]
      exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
    | succ s =>
      exact False.elim (Finset.notMem_empty _ (x ⟨0, Nat.succ_pos s⟩).property)
  · intro f hf j hj hr
    let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ x : VH, z = Sum.inl x ∧ B.sourceCluster x = j
    let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j
    let P : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
      ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧ A.allowed x v
    let W : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
      ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧
        (x, v) ∈ UpdatedCandidacyCluster B A ∅ f j
    letI : DecidableRel P.Adj := Classical.decRel _
    letI : DecidableRel W.Adj := Classical.decRel _
    -- Restriction preserves every edge count used by super-regularity on these parts.
    have hadj : ∀ p ∈ L, ∀ s ∈ Q, W.Adj p s ↔ P.Adj p s := by
      intro p hp s hs
      obtain ⟨x, rfl, hx⟩ := (Finset.mem_filter.mp hp).2
      obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hs).2
      simp [W, P, SimpleGraph.fromRel_adj, UpdatedCandidacyCluster, UpdatedCandidacy,
        hx, hv]
    have hleft : ∀ p ∈ L, Q.filter (fun s => W.Adj p s) =
        Q.filter (fun s => P.Adj p s) := by
      intro p hp
      ext s
      simp only [Finset.mem_filter]
      exact and_congr_right fun hs => hadj p hp s hs
    have hright : ∀ s ∈ Q, L.filter (fun p => W.Adj p s) =
        L.filter (fun p => P.Adj p s) := by
      intro s hs
      ext p
      simp only [Finset.mem_filter]
      exact and_congr_right fun hp => hadj p hp s hs
    have hdens : ∀ U ⊆ L, ∀ V ⊆ Q, PairDensity W U V = PairDensity P U V := by
      intro U hU V hV
      have he : (U.product V).filter (fun p => W.Adj p.1 p.2) =
          (U.product V).filter (fun p => P.Adj p.1 p.2) := by
        ext p
        simp only [Finset.mem_filter]
        refine and_congr_right fun hp => ?_
        obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
        exact hadj p.1 (hU hu) p.2 (hV hv)
      unfold PairDensity
      rw [he]
    have hsuper : SuperRegularPair W L Q (epsilon 0) d := by
      have hp : SuperRegularPair P L Q (epsilon 0) d := hA j
      refine ⟨?_, ?_, ?_⟩
      · intro U hU V hV hu hv
        rw [hdens U hU V hV]
        exact hp.1 U hU V hV hu hv
      · intro p hpL
        rw [hleft p hpL]
        exact hp.2.1 p hpL
      · intro s hsQ
        rw [hright s hsQ]
        exact hp.2.2 s hsQ
    dsimp
    simp only [Nat.not_lt_zero, Finset.notMem_empty, or_self, false_and,
      Finset.filter_false, Finset.card_empty, Finset.filter_empty,
      and_true, not_false_eq_true, hdensity]
    exact ⟨Nat.zero_le D, by decide, W, le_rfl, hsuper⟩
