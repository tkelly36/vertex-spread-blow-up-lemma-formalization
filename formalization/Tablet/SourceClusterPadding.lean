import Tablet.PaddedSource
import Tablet.CandidacyLowerSuperRegular
import Tablet.InstanceLowerSuperRegular
import Tablet.CompatibleEmbedding
import Tablet.VertexSpreadOn
import Tablet.VertexSpreadRestriction
import Tablet.CompleteRowPadding
import Mathlib.Combinatorics.SimpleGraph.Sum

-- [TABLET NODE: SourceClusterPadding]
theorem SourceClusterPadding :
    ∀ {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
      [DecidableEq VH] [DecidableEq VG]
      {H : SimpleGraph VH} {G : SimpleGraph VG}
      [DecidableRel H.Adj] [DecidableRel G.Adj]
      {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
      (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
      [DecidableRel A.allowed] (ε η d : ENNReal),
      0 < ε → ε ≤ η * η → η ≤ 1 → d ≤ 1 →
      CandidacyLowerSuperRegular B A ε d →
      ∃ (Hp : SimpleGraph (PaddedSource B)),
      ∃ _hHp : DecidableRel Hp.Adj,
      ∃ Bp : BlowUpInstance r (PaddedSource B) VG Hp G R,
      ∃ Ap : CandidacySystem Bp,
      ∃ _hAp : DecidableRel Ap.allowed,
        (∀ x y : VH, Hp.Adj (Sum.inl x) (Sum.inl y) ↔ H.Adj x y) ∧
        (∀ z w, Hp.Adj z w → ∃ x y : VH, z = Sum.inl x ∧ w = Sum.inl y) ∧
        (∀ x : VH, Bp.sourceCluster (Sum.inl x) = B.sourceCluster x) ∧
        (∀ (i : Fin r) (k : Fin (Fintype.card
            {v : VG // B.hostCluster v = i} - Fintype.card
            {x : VH // B.sourceCluster x = i})),
          Bp.sourceCluster (Sum.inr ⟨i, k⟩) = i) ∧
        (∀ v, Bp.hostCluster v = B.hostCluster v) ∧
        (∀ x v, Ap.allowed (Sum.inl x) v ↔ A.allowed x v) ∧
        (∀ (i : Fin r) (k : Fin (Fintype.card
            {v : VG // B.hostCluster v = i} - Fintype.card
            {x : VH // B.sourceCluster x = i})) (v : VG),
          Ap.allowed (Sum.inr ⟨i, k⟩) v ↔ B.hostCluster v = i) ∧
        (∀ i, Fintype.card {z : PaddedSource B // Bp.sourceCluster z = i} =
          Fintype.card {v : VG // Bp.hostCluster v = i}) ∧
        Hp.maxDegree ≤ H.maxDegree ∧
        (∀ δ, InstanceLowerSuperRegular B δ d →
          InstanceLowerSuperRegular Bp δ d) ∧
        CandidacyLowerSuperRegular Bp Ap η d ∧
        (∀ φ : SimpleGraph.Copy Hp G, CompatibleEmbedding Bp Ap φ →
          ∃ ψ : SimpleGraph.Copy H G, CompatibleEmbedding B A ψ ∧
            ∀ x, ψ x = φ (Sum.inl x)) ∧
        (∀ (q : ENNReal) (μ : PMF {φ : SimpleGraph.Copy Hp G // CompatibleEmbedding Bp Ap φ}),
          VertexSpreadOn (μ.map fun φ => fun z => φ.1 z) q Set.univ →
          ∃ ν : PMF {ψ : SimpleGraph.Copy H G // CompatibleEmbedding B A ψ},
            VertexSpreadOn (ν.map fun ψ => fun x => ψ.1 x) q Set.univ) := by
-- BODY
  classical
  intro r VH VG _ _ _ _ H G _ _ R _ B A _ ε η d hε hbudget hη hd hA
  let K := fun i : Fin r => Fintype.card {v : VG // B.hostCluster v = i} -
    Fintype.card {x : VH // B.sourceCluster x = i}
  let Hp : SimpleGraph (PaddedSource B) := H.sum ⊥
  letI : DecidableRel Hp.Adj := Classical.decRel _
  let c : PaddedSource B → Fin r := Sum.elim B.sourceCluster Sigma.fst
  have hcard (i : Fin r) : Fintype.card {z : PaddedSource B // c z = i} =
      Fintype.card {v : VG // B.hostCluster v = i} := by
    rw [Fintype.card_congr (Equiv.subtypeSum), Fintype.card_sum]
    change Fintype.card {x : VH // B.sourceCluster x = i} +
      Fintype.card {s : (Σ j : Fin r, Fin (K j)) // s.1 = i} = _
    rw [Fintype.card_congr (Equiv.sigmaSubtype i), Fintype.card_fin]
    exact Nat.add_sub_of_le (B.capacity i)
  have hsupp : ∀ {z w : PaddedSource B}, Hp.Adj z w → R.Adj (c z) (c w) := by
    rintro (x | x) (y | y) h
    · exact B.reduced_support h
    · simpa [Hp] using h
    · simpa [Hp] using h
    · simpa [Hp] using h
  let Bp : BlowUpInstance r (PaddedSource B) VG Hp G R := {
    sourceCluster := c
    hostCluster := B.hostCluster
    source_independent := by
      intro i
      rw [SimpleGraph.isIndepSet_iff]
      intro z hz w hw _ hzw
      have hR := hsupp hzw
      change c z = i at hz
      change c w = i at hw
      rw [hz, hw] at hR
      exact R.loopless.irrefl i hR
    capacity := fun i => (hcard i).le
    reduced_support := hsupp }
  let Ap : CandidacySystem Bp := {
    allowed := fun z v => match z with
      | Sum.inl x => A.allowed x v
      | Sum.inr s => B.hostCluster v = s.1
    cluster_respecting := by
      rintro (x | s) v h
      · exact A.cluster_respecting h
      · exact h.symm }
  letI : DecidableRel Ap.allowed := fun z v => Classical.propDecidable _
  have degreeold (x : VH) : Hp.degree (Sum.inl x) = H.degree x := by
    have hn : Hp.neighborFinset (Sum.inl x) =
        (H.neighborFinset x).map (Function.Embedding.inl) := by
      ext z
      cases z <;> simp [Hp, SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.degree, hn, Finset.card_map]
  have degreedummy (s : Σ i : Fin r, Fin (K i)) : Hp.degree (Sum.inr s) = 0 := by
    apply SimpleGraph.IsIsolated.degree_eq_zero
    intro z
    cases z <;> simp [Hp]
  have hmax : Hp.maxDegree ≤ H.maxDegree := by
    apply SimpleGraph.maxDegree_le_of_forall_degree_le
    rintro (x | s)
    · rw [degreeold]; exact H.degree_le_maxDegree x
    · rw [degreedummy]; exact Nat.zero_le _
  have hpad : CandidacyLowerSuperRegular Bp Ap η d := by
    intro i
    let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ x : VH, z = Sum.inl x ∧ B.sourceCluster x = i
    let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = i
    let Lp : Finset ((PaddedSource B) ⊕ VG) := Finset.univ.filter fun z =>
      ∃ x : PaddedSource B, z = Sum.inl x ∧ c x = i
    let Qp : Finset ((PaddedSource B) ⊕ VG) := Finset.univ.filter fun z =>
      ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = i
    let D : Finset ((PaddedSource B) ⊕ VG) := Finset.univ.filter fun z =>
      ∃ s : (Σ j : Fin r, Fin (K j)), z = Sum.inl (Sum.inr s) ∧ s.1 = i
    let e : (VH ⊕ VG) ↪ ((PaddedSource B) ⊕ VG) := {
      toFun := Sum.map Sum.inl id
      inj' := by
        rintro (x | v) (y | w) h
        · exact congrArg Sum.inl (Sum.inl_injective (Sum.inl_injective h))
        · cases h
        · cases h
        · exact congrArg Sum.inr (Sum.inr_injective h) }
    let F : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
      ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ q = Sum.inr v ∧ A.allowed x v
    let Fp : SimpleGraph ((PaddedSource B) ⊕ VG) := SimpleGraph.fromRel fun p q =>
      ∃ x : PaddedSource B, ∃ v : VG, p = Sum.inl x ∧ q = Sum.inr v ∧ Ap.allowed x v
    letI : DecidableRel F.Adj := Classical.decRel _
    letI : DecidableRel Fp.Adj := Classical.decRel _
    have leq : Lp = (L.map e) ∪ D := by
      ext z
      constructor
      · intro hz
        obtain ⟨x, rfl, hx⟩ := (Finset.mem_filter.mp hz).2
        rcases x with (x | s)
        · apply Finset.mem_union_left
          exact Finset.mem_map.mpr ⟨Sum.inl x,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, rfl, hx⟩, rfl⟩
        · apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, rfl, hx⟩
      · intro hz
        rcases Finset.mem_union.mp hz with ho | hd'
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ho
          obtain ⟨x', rfl, hx'⟩ := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Sum.inl x', rfl, hx'⟩
        · obtain ⟨s, rfl, hs⟩ := (Finset.mem_filter.mp hd').2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Sum.inr s, rfl, hs⟩
    have qeq : Qp = Q.map e := by
      ext z
      constructor
      · intro hz
        obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hz).2
        exact Finset.mem_map.mpr ⟨Sum.inr v,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, rfl, hv⟩, rfl⟩
      · intro hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, rfl, hv⟩
    have hdis : Disjoint (L.map e) D := by
      apply Finset.disjoint_left.mpr
      intro z hz hd'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨x', rfl, _⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨s, heq, _⟩ := (Finset.mem_filter.mp hd').2
      change Sum.inl (Sum.inl x') = Sum.inl (Sum.inr s) at heq
      simp only [Sum.inl.injEq, Sum.inl_ne_inr] at heq
    have lpmap : Lp = (Finset.univ.filter fun z : PaddedSource B => c z = i).map
        Function.Embedding.inl := by
      ext z
      cases z <;> simp only [Lp, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Function.Embedding.inl_apply, Sum.inl.injEq,
        Sum.inr_ne_inl, Sum.inl_ne_inr, exists_eq_left, exists_eq_right,
        exists_eq_left', false_and, and_false, exists_false]
    have qmap : Q = (Finset.univ.filter fun v : VG => B.hostCluster v = i).map
        Function.Embedding.inr := by
      ext z
      cases z <;> simp [Q]
    have hsize : ((L.map e) ∪ D).card = Q.card := by
      rw [← leq, lpmap, qmap, Finset.card_map, Finset.card_map,
        ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact hcard i
    have hcopy : ∀ x ∈ L, ∀ y ∈ Q, Fp.Adj (e x) (e y) ↔ F.Adj x y := by
      intro x hx y hy
      obtain ⟨x', rfl, _⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨v, rfl, _⟩ := (Finset.mem_filter.mp hy).2
      simp [Fp, F, e, Ap]
    have hcomplete : ∀ z ∈ D, ∀ y ∈ Q, Fp.Adj z (e y) := by
      intro z hz y hy
      obtain ⟨s, rfl, hs⟩ := (Finset.mem_filter.mp hz).2
      obtain ⟨v, rfl, hv⟩ := (Finset.mem_filter.mp hy).2
      change Fp.Adj (Sum.inl (Sum.inr s)) (Sum.inr v)
      refine ⟨by simp, Or.inl ⟨Sum.inr s, v, rfl, rfl, ?_⟩⟩
      exact hv.trans hs.symm
    have result := CompleteRowPadding F Fp e L Q D ε η d hε hbudget hη hd
      hdis hsize hcopy hcomplete (hA i)
    rw [← leq, ← qeq] at result
    exact result
  let restrict : SimpleGraph.Copy Hp G → SimpleGraph.Copy H G := fun φ => {
    toHom := {
      toFun := fun x => φ (Sum.inl x)
      map_rel' := fun {x y} h => φ.toHom.map_rel h }
    injective' := φ.injective.comp Sum.inl_injective }
  have compatible (φ : SimpleGraph.Copy Hp G) (hφ : CompatibleEmbedding Bp Ap φ) :
      CompatibleEmbedding B A (restrict φ) := fun x => hφ (Sum.inl x)
  refine ⟨Hp, inferInstance, Bp, Ap, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hmax, ?_, hpad, ?_, ?_⟩
  · intro x y; rfl
  · rintro (x | s) (y | t) h
    · exact ⟨x, y, rfl, rfl⟩
    · simpa [Hp] using h
    · simpa [Hp] using h
    · simpa [Hp] using h
  · intro x; rfl
  · intro i k; rfl
  · intro v; rfl
  · intro x v; rfl
  · intro i k v; rfl
  · exact hcard
  · intro δ hδ; exact hδ
  · intro φ hφ
    exact ⟨restrict φ, compatible φ hφ, fun x => rfl⟩
  · intro q μ hμ
    let f : {φ : SimpleGraph.Copy Hp G // CompatibleEmbedding Bp Ap φ} →
        {ψ : SimpleGraph.Copy H G // CompatibleEmbedding B A ψ} :=
      fun φ => ⟨restrict φ.1, compatible φ.1 φ.2⟩
    refine ⟨μ.map f, ?_⟩
    have hr := VertexSpreadRestriction (Function.Embedding.inl : VH ↪ PaddedSource B) hμ
    simpa only [PMF.map_comp] using hr
