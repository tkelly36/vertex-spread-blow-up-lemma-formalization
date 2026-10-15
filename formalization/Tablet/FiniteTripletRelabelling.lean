import Tablet.NearEqualRegularTriplet
import Tablet.MatchingInducedGraph
import Tablet.PerfectMatching
import Tablet.SuperRegularPairEmbedding

-- [TABLET NODE: FiniteTripletRelabelling]
theorem FiniteTripletRelabelling
    {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V']
    (e : V ≃ V') (F : SimpleGraph V) [DecidableRel F.Adj]
    (U K : Finset V) (hUK : Disjoint U K) :
    let U' := U.image e
    let K' := K.image e
    let F' := F.comap e.symm
    ∃ (eU : U ≃ U') (eK : K ≃ K') (hUK' : Disjoint U' K')
      (eM : {sigma : U → K // PerfectMatching F U K hUK sigma} ≃
        {sigma : U' → K' // PerfectMatching F' U' K' hUK' sigma}),
      (∀ u, (eU u : V') = e u) ∧
      (∀ k, (eK k : V') = e k) ∧
      (∀ sigma u, (eM sigma).val (eU u) = eK (sigma.val u)) ∧
      (∀ eps d, SuperRegularPair F U K eps d ↔ SuperRegularPair F' U' K' eps d) ∧
      (∀ (F13 F23 : SimpleGraph V) [DecidableRel F13.Adj] [DecidableRel F23.Adj]
        (Z : Finset V) (m : ℕ) (eps d12 d13 d23 : ENNReal),
        NearEqualRegularTriplet F F13 F23 U K Z m eps d12 d13 d23 ↔
        NearEqualRegularTriplet F' (F13.comap e.symm) (F23.comap e.symm)
          U' K' (Z.image e) m eps d12 d13 d23) ∧
      (∀ (F13 F23 : SimpleGraph V) [DecidableRel F13.Adj] [DecidableRel F23.Adj]
        (Z : Finset V) (sigma : {sigma : U → K // PerfectMatching F U K hUK sigma})
        (eps d : ENNReal),
        let I := MatchingInducedGraph F13 F23 U K Z sigma.val
        let I' := MatchingInducedGraph (F13.comap e.symm) (F23.comap e.symm)
          U' K' (Z.image e) (eM sigma).val
        @SuperRegularPair _ _ I (Classical.decRel _)
          (Finset.univ.image (Sum.inl : U → U ⊕ Z))
          (Finset.univ.image (Sum.inr : Z → U ⊕ Z)) eps d ↔
        @SuperRegularPair _ _ I' (Classical.decRel _)
          (Finset.univ.image (Sum.inl : U' → U' ⊕ Z.image e))
          (Finset.univ.image (Sum.inr : Z.image e → U' ⊕ Z.image e)) eps d) := by
-- BODY
  classical
  dsimp only
  let part (S : Finset V) : S ≃ S.image e :=
    { toFun := fun x => ⟨e x, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩
      invFun := fun y => ⟨e.symm y, by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
        simpa [← hxy] using hx⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  let eU := part U
  let eK := part K
  have coePart (S : Finset V) (x : S) : ((part S) x : V') = e x := rfl
  have hUK' : Disjoint (U.image e) (K.image e) :=
    (Finset.disjoint_image e.injective).mpr hUK
  let push (sigma : {sigma : U → K // PerfectMatching F U K hUK sigma}) :
      {sigma : U.image e → K.image e //
        PerfectMatching (F.comap e.symm) (U.image e) (K.image e) hUK' sigma} :=
    ⟨fun x => eK (sigma.val (eU.symm x)), by
      refine ⟨eK.bijective.comp (sigma.property.1.comp eU.symm.bijective), ?_⟩
      intro x
      change F.Adj (e.symm x) (e.symm (e (sigma.val (eU.symm x))))
      simpa only [e.symm_apply_apply] using sigma.property.2 (eU.symm x)⟩
  let pull (sigma : {sigma : U.image e → K.image e //
        PerfectMatching (F.comap e.symm) (U.image e) (K.image e) hUK' sigma}) :
      {sigma : U → K // PerfectMatching F U K hUK sigma} :=
    ⟨fun x => eK.symm (sigma.val (eU x)), by
      refine ⟨eK.symm.bijective.comp (sigma.property.1.comp eU.bijective), ?_⟩
      intro x
      have h := sigma.property.2 (eU x)
      change F.Adj (e.symm (e x)) (e.symm (sigma.val (eU x))) at h
      simpa only [e.symm_apply_apply] using h⟩
  let eM :=
    { toFun := push
      invFun := pull
      left_inv := fun sigma => by
        apply Subtype.ext
        funext x
        change eK.symm (eK (sigma.val (eU.symm (eU x)))) = sigma.val x
        simp only [Equiv.symm_apply_apply]
      right_inv := fun sigma => by
        apply Subtype.ext
        funext x
        change eK (eK.symm (sigma.val (eU (eU.symm x)))) = sigma.val x
        simp only [Equiv.apply_symm_apply] :
      {sigma : U → K // PerfectMatching F U K hUK sigma} ≃
        {sigma : U.image e → K.image e //
          PerfectMatching (F.comap e.symm) (U.image e) (K.image e) hUK' sigma} }
  have eval (sigma : {sigma : U → K // PerfectMatching F U K hUK sigma}) (u : U) :
      (eM sigma).val (eU u) = eK (sigma.val u) := by
    change eK (sigma.val (eU.symm (eU u))) = _
    rw [eU.symm_apply_apply]
  have card (S : Finset V) : (S.image e).card = S.card :=
    Finset.card_image_of_injective S e.injective
  have sr (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V)
      (eps d : ENNReal) :
      SuperRegularPair G L R eps d ↔
        SuperRegularPair (G.comap e.symm) (L.image e) (R.image e) eps d := by as_aux_lemma =>
    constructor
    · exact SuperRegularPairEmbedding e e.injective G (G.comap e.symm)
        L R eps d (fun x _ y _ => by simp)
    · intro h
      have hh := SuperRegularPairEmbedding e.symm e.symm.injective (G.comap e.symm) G
        (L.image e) (R.image e) eps d (fun x _ y _ => Iff.rfl) h
      simpa only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
        Finset.image_id'] using hh
  refine ⟨eU, eK, hUK', eM, coePart U, coePart K, eval, sr F U K, ?_, ?_⟩
  · intro F13 F23 _ _ Z m eps d12 d13 d23
    have common (v u : V) :
        (((Z.image e).filter fun z =>
          (F13.comap e.symm).Adj (e v) z ∧ (F23.comap e.symm).Adj (e u) z).card) =
        (Z.filter fun z => F13.Adj v z ∧ F23.Adj u z).card := by
      rw [Finset.filter_image]
      simpa only [SimpleGraph.comap_adj, Equiv.symm_apply_apply] using
        card (Z.filter fun z => F13.Adj v z ∧ F23.Adj u z)
    have hc :
        (∀ v ∈ U, ∀ u ∈ K, F.Adj v u →
          (d13 * d23 - eps) * Z.card ≤
            ((Z.filter fun z => F13.Adj v z ∧ F23.Adj u z).card : ENNReal) ∧
          ((Z.filter fun z => F13.Adj v z ∧ F23.Adj u z).card : ENNReal) ≤
            (d13 * d23 + eps) * Z.card) ↔
        (∀ v ∈ U.image e, ∀ u ∈ K.image e, (F.comap e.symm).Adj v u →
          (d13 * d23 - eps) * (Z.image e).card ≤
            (((Z.image e).filter fun z =>
              (F13.comap e.symm).Adj v z ∧ (F23.comap e.symm).Adj u z).card : ENNReal) ∧
          (((Z.image e).filter fun z =>
              (F13.comap e.symm).Adj v z ∧ (F23.comap e.symm).Adj u z).card : ENNReal) ≤
            (d13 * d23 + eps) * (Z.image e).card) := by as_aux_lemma =>
      constructor
      · intro h v hv u hu hAdj
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
        simpa only [card, common] using h a ha b hb (by simpa using hAdj)
      · intro h v hv u hu hAdj
        have hh := h (e v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
          (e u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩) (by simpa using hAdj)
        simpa only [card, common] using hh
    simp only [NearEqualRegularTriplet, card, Finset.disjoint_image e.injective,
      ← sr]
    repeat' apply and_congr_right; intro _
    simpa only [card] using hc
  · intro F13 F23 _ _ Z sigma eps d
    let eZ := part Z
    let t := Equiv.sumCongr eU eZ
    let I := MatchingInducedGraph F13 F23 U K Z sigma.val
    let J := MatchingInducedGraph (F13.comap e.symm) (F23.comap e.symm)
      (U.image e) (K.image e) (Z.image e) (eM sigma).val
    have cross (u : U) (z : Z) :
        J.Adj (t (Sum.inl u)) (t (Sum.inr z)) ↔ I.Adj (Sum.inl u) (Sum.inr z) := by as_aux_lemma =>
      simp only [I, J, t, MatchingInducedGraph, SimpleGraph.fromRel_adj,
        Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        ne_eq, reduceCtorEq, not_false_eq_true, true_and,
        Sum.inl.injEq, Sum.inr.injEq, false_and, exists_false, or_false,
        exists_and_left, exists_eq_left', SimpleGraph.comap_adj]
      rw [eval]
      simp only [eU, eK, eZ, coePart, Equiv.symm_apply_apply]
    have hadj : ∀ x y, J.Adj (t x) (t y) ↔ I.Adj x y := by as_aux_lemma =>
      intro x y
      cases x with
      | inl u =>
        cases y with
        | inl v =>
          simp only [I, J, t, MatchingInducedGraph, SimpleGraph.fromRel_adj,
            Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq,
            reduceCtorEq, and_false, false_and, exists_false, or_self]
        | inr z => exact cross u z
      | inr z =>
        cases y with
        | inl u =>
          exact ⟨fun h => ((cross u z).mp h.symm).symm,
            fun h => ((cross u z).mpr h.symm).symm⟩
        | inr w =>
          simp only [I, J, t, MatchingInducedGraph, SimpleGraph.fromRel_adj,
            Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq,
            reduceCtorEq, and_false, false_and, exists_false, or_self]
    have hl :
        (Finset.univ.image (Sum.inl : U → U ⊕ Z)).image t =
          Finset.univ.image (Sum.inl : U.image e → U.image e ⊕ Z.image e) := by
      ext x
      cases x with
      | inl u =>
        simp [Finset.image_image, t, Function.comp_def]
        exact ⟨(eU.symm u).val, (eU.symm u).property, eU.apply_symm_apply u⟩
      | inr z => simp [Finset.image_image, t, Function.comp_def]
    have hr :
        (Finset.univ.image (Sum.inr : Z → U ⊕ Z)).image t =
          Finset.univ.image (Sum.inr : Z.image e → U.image e ⊕ Z.image e) := by
      ext x
      cases x with
      | inl u => simp [Finset.image_image, t, Function.comp_def]
      | inr z =>
        simp [Finset.image_image, t, Function.comp_def]
        exact ⟨(eZ.symm z).val, (eZ.symm z).property, eZ.apply_symm_apply z⟩
    constructor
    · intro h
      have hh := SuperRegularPairEmbedding t t.injective I J _ _ eps d
        (fun x _ y _ => hadj x y) h
      simpa only [hl, hr] using hh
    · intro h
      rw [← hl, ← hr] at h
      have hh := SuperRegularPairEmbedding t.symm t.symm.injective J I _ _ eps d
        (fun x _ y _ => by simpa only [t.apply_symm_apply] using
          (hadj (t.symm x) (t.symm y)).symm) h
      simpa only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
        Finset.image_id'] using hh
