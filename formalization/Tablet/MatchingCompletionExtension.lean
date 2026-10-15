import Tablet.BlowUpInstance
import Tablet.SaturatingSourcePair
import Tablet.FinitePartialMatchingCompletion
import Tablet.FiberwiseCapacityRefinement

-- [TABLET NODE: MatchingCompletionExtension]
theorem MatchingCompletionExtension :
    ∀ (Delta r n : ℕ), 1 ≤ Delta →
      ∀ {VH VG : Type*} [Fintype VH] [Fintype VG] [DecidableEq VH]
        {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
        [DecidableRel H.Adj] [DecidableRel R.Adj]
        (B : BlowUpInstance r VH VG H G R)
        (color : VH → Fin (Delta ^ 2)),
        (∀ i j,
          let s := Finset.univ.filter fun x : VH =>
            B.sourceCluster x = i ∧ color x = j
          s.card = n / (Delta ^ 2) ∨ s.card = n / (Delta ^ 2) + 1) →
        (∀ {x y}, B.sourceCluster x = B.sourceCluster y → color x = color y →
          x ≠ y → ¬ H.Adj x y ∧ ¬ ∃ z, H.Adj x z ∧ H.Adj y z) →
        R.maxDegree ≤ Delta →
        ∃ (H' : SimpleGraph VH) (R' : SimpleGraph (Fin r × Fin (Delta ^ 2)))
          (_ : DecidableRel H'.Adj) (_ : DecidableRel R'.Adj)
          (B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G
            (R'.comap finProdFinEquiv.symm)),
          H ≤ H' ∧
          (∀ x, finProdFinEquiv.symm (B'.sourceCluster x) =
            (B.sourceCluster x, color x)) ∧
          (∀ p q, R'.Adj p q ↔ R.Adj p.1 q.1) ∧
          R'.maxDegree ≤ Delta ^ 3 ∧
          ∀ p q, R'.Adj p q →
            SaturatingSourcePair B'
              (finProdFinEquiv p)
              (finProdFinEquiv q) := by
-- BODY
  intro Delta r n hDelta VH VG _ _ _ H G R _ _ B color _htwoSizes htwo hR
  classical
  let P := Fin r × Fin (Delta ^ 2)
  let E : P ≃ Fin (r * Delta ^ 2) := finProdFinEquiv
  let part : VH → P := fun x => (B.sourceCluster x, color x)
  let X (p : P) := {x : VH // part x = p}
  have hleft (p q : P) (x : X p) (y z : X q)
      (hxy : H.Adj x.val y.val) (hxz : H.Adj x.val z.val) : y = z := by
    apply Subtype.ext
    by_contra hne
    have hp : part y.val = part z.val := y.property.trans z.property.symm
    exact (htwo (congrArg Prod.fst hp) (congrArg Prod.snd hp) hne).2
      ⟨x.val, H.symm hxy, H.symm hxz⟩
  have hright (p q : P) (x y : X p) (z : X q)
      (hxz : H.Adj x.val z.val) (hyz : H.Adj y.val z.val) : x = y := by
    apply Subtype.ext
    by_contra hne
    have hp : part x.val = part y.val := x.property.trans y.property.symm
    exact (htwo (congrArg Prod.fst hp) (congrArg Prod.snd hp) hne).2
      ⟨z.val, hxz, hyz⟩
  have hcomplete (p q : P) : ∃ C : X p → X q → Prop,
      (∀ x y, H.Adj x.val y.val → C x y) ∧
      ((∃ τ : X p ↪ X q, ∀ x y, C x y ↔ y = τ x) ∨
       (∃ τ : X q ↪ X p, ∀ x y, C x y ↔ x = τ y)) := by
    by_cases hcard : Fintype.card (X p) ≤ Fintype.card (X q)
    · obtain ⟨τ, hτ⟩ := FinitePartialMatchingCompletion
        (fun x : X p => fun y : X q => H.Adj x.val y.val)
        (hleft p q) (hright p q) hcard
      exact ⟨fun x y => y = τ x, fun x y h => (hτ x y h).symm,
        Or.inl ⟨τ, fun _ _ => Iff.rfl⟩⟩
    · obtain ⟨τ, hτ⟩ := FinitePartialMatchingCompletion
        (fun y : X q => fun x : X p => H.Adj x.val y.val)
        (fun y x z h₁ h₂ => hright p q x z y h₁ h₂)
        (fun y z x h₁ h₂ => hleft p q x y z h₁ h₂)
        (Nat.le_of_lt (Nat.lt_of_not_ge hcard))
      exact ⟨fun x y => x = τ y, fun x y h => (hτ y x h).symm,
        Or.inr ⟨τ, fun _ _ => Iff.rfl⟩⟩
  choose C hCold hC using hcomplete
  -- Only the completion indexed by the increasing ordered pair is used.
  let H' : SimpleGraph VH :=
    { Adj := fun x y => R.Adj (B.sourceCluster x) (B.sourceCluster y) ∧
        ((E (part x) < E (part y) ∧
          C (part x) (part y) ⟨x, rfl⟩ ⟨y, rfl⟩) ∨
         (E (part y) < E (part x) ∧
          C (part y) (part x) ⟨y, rfl⟩ ⟨x, rfl⟩))
      symm := by
        intro x y h
        exact ⟨R.symm h.1, h.2.symm⟩
      loopless := by
        constructor
        intro x h
        exact R.loopless.irrefl _ h.1 }
  let R' : SimpleGraph P :=
    { Adj := fun p q => R.Adj p.1 q.1
      symm := fun _ _ h => R.symm h
      loopless := ⟨fun _ h => R.loopless.irrefl _ h⟩ }
  have hle : H ≤ H' := by
    intro x y hxy
    have hr := B.reduced_support hxy
    have hne : E (part x) ≠ E (part y) := by
      intro h
      have hp := E.injective h
      exact R.ne_of_adj hr (congrArg Prod.fst hp)
    refine ⟨hr, ?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨h, hCold _ _ _ _ hxy⟩
    · exact Or.inr ⟨h, hCold _ _ _ _ (H.symm hxy)⟩
  have hAdj (p q : P) (hr : R'.Adj p q) (hlt : E p < E q)
      (x : X p) (y : X q) : H'.Adj x.val y.val ↔ C p q x y := by
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    subst p
    subst q
    change (R.Adj (B.sourceCluster x) (B.sourceCluster y) ∧
      ((E (part x) < E (part y) ∧ _) ∨ (E (part y) < E (part x) ∧ _))) ↔ _
    simp only [show R.Adj (B.sourceCluster x) (B.sourceCluster y) from hr,
      hlt, not_lt_of_ge (le_of_lt hlt), true_and, false_and, or_false]
  obtain ⟨e⟩ : Nonempty (∀ i, {x : VH // B.sourceCluster x = i} ↪
      {v : VG // B.hostCluster v = i}) := by
    exact ⟨fun i => (Function.Embedding.nonempty_of_card_le (B.capacity i)).some⟩
  let j₀ : Fin (Delta ^ 2) := ⟨0, by positivity⟩
  obtain ⟨d, hd⟩ := FiberwiseCapacityRefinement
    B.sourceCluster B.hostCluster color j₀ e
  let B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G
      (R'.comap E.symm) :=
    { sourceCluster := fun x => E (part x)
      hostCluster := fun v => E (B.hostCluster v, d v)
      source_independent := by
        intro i x hx y hy _ hxy
        have hp : part x = part y := E.injective (hx.trans hy.symm)
        exact R.ne_of_adj hxy.1 (congrArg Prod.fst hp)
      capacity := by
        intro t
        let es : {x : VH // E (part x) = t} ≃
            {x : VH // B.sourceCluster x = (E.symm t).1 ∧
              color x = (E.symm t).2} :=
          Equiv.subtypeEquivRight (fun _ =>
            E.apply_eq_iff_eq_symm_apply.trans Prod.ext_iff)
        let ev : {v : VG // E (B.hostCluster v, d v) = t} ≃
            {v : VG // B.hostCluster v = (E.symm t).1 ∧
              d v = (E.symm t).2} :=
          Equiv.subtypeEquivRight (fun _ =>
            E.apply_eq_iff_eq_symm_apply.trans Prod.ext_iff)
        exact (Fintype.card_congr es).le.trans
          ((hd (E.symm t).1 (E.symm t).2).trans (Fintype.card_congr ev).symm.le)
      reduced_support := by
        intro x y hxy
        change R'.Adj (E.symm (E (part x))) (E.symm (E (part y)))
        simpa only [Equiv.symm_apply_apply] using hxy.1 }
  let ef (p : P) : X p ≃ {x : VH // B'.sourceCluster x = E p} :=
    Equiv.subtypeEquivRight (fun x => by
      change part x = p ↔ E (part x) = E p
      exact ⟨congrArg E, fun h => E.injective h⟩)
  have hsat (p q : P) (hr : R'.Adj p q) (hlt : E p < E q) :
      SaturatingSourcePair B' (E p) (E q) := by
    rcases hC p q with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
    · refine Or.inl ⟨((ef p).symm.toEmbedding.trans τ).trans (ef q).toEmbedding, ?_⟩
      intro x y
      change H'.Adj x.val y.val ↔ y = (ef q) (τ ((ef p).symm x))
      exact ((hAdj p q hr hlt ((ef p).symm x) ((ef q).symm y)).trans
        (hτ _ _)).trans (ef q).symm.apply_eq_iff_eq_symm_apply
    · refine Or.inr ⟨((ef q).symm.toEmbedding.trans τ).trans (ef p).toEmbedding, ?_⟩
      intro x y
      change H'.Adj x.val y.val ↔ x = (ef p) (τ ((ef q).symm y))
      exact ((hAdj p q hr hlt ((ef p).symm x) ((ef q).symm y)).trans
        (hτ _ _)).trans (ef p).symm.apply_eq_iff_eq_symm_apply
  have hsatSymm (i j : Fin (r * Delta ^ 2))
      (h : SaturatingSourcePair B' i j) : SaturatingSourcePair B' j i := by
    rcases h with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
    · exact Or.inr ⟨τ, fun x y => (H'.adj_comm _ _).trans (hτ y x)⟩
    · exact Or.inl ⟨τ, fun x y => (H'.adj_comm _ _).trans (hτ y x)⟩
  have hdegree : R'.maxDegree ≤ Delta ^ 3 := by
    apply R'.maxDegree_le_of_forall_degree_le
    intro p
    let en : R'.neighborSet p ≃ R.neighborSet p.1 × Fin (Delta ^ 2) :=
      { toFun := fun q => (⟨q.val.1, q.property⟩, q.val.2)
        invFun := fun q => ⟨(q.1.val, q.2), q.1.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      R'.degree p = Fintype.card (R'.neighborSet p) :=
        (R'.card_neighborSet_eq_degree p).symm
      _ = Fintype.card (R.neighborSet p.1 × Fin (Delta ^ 2)) := Fintype.card_congr en
      _ = R.degree p.1 * Delta ^ 2 := by
        rw [Fintype.card_prod, R.card_neighborSet_eq_degree, Fintype.card_fin]
      _ ≤ Delta * Delta ^ 2 :=
        Nat.mul_le_mul_right _ ((R.degree_le_maxDegree p.1).trans hR)
      _ = Delta ^ 3 := by rw [pow_succ]; exact Nat.mul_comm _ _
  refine ⟨H', R', inferInstance, inferInstance, B', hle, ?_, ?_, hdegree, ?_⟩
  · intro x
    exact E.symm_apply_apply (part x)
  · intro p q
    rfl
  · intro p q hr
    by_cases hlt : E p < E q
    · exact hsat p q hr hlt
    · have hne : E p ≠ E q := fun h => R'.ne_of_adj hr (E.injective h)
      exact hsatSymm _ _ (hsat q p (R'.symm hr) (lt_of_le_of_ne (le_of_not_gt hlt) hne.symm))
