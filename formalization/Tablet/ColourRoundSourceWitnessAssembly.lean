import Tablet.ColourRoundStepParameters
import Tablet.SaturatingSourcePair
import Tablet.EqualSizeSourceWitnessTransport
import Tablet.CurrentExtraSourceWitnessTransport
import Tablet.FutureExtraSourceWitnessTransport

-- [TABLET NODE: ColourRoundSourceWitnessAssembly]
theorem ColourRoundSourceWitnessAssembly
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (theta density epsilon rho eta omega xi : ℕ → ENNReal)
    (D : ℕ) (d C a : ENNReal) (n round y : ℕ)
    (P : ColourRoundStepParameters D q d C a n round
      theta density epsilon rho eta omega xi)
    (hn : 1 ≤ n) (hy : y < D)
    (i j : Fin r) (hij : R.Adj i j)
    (hsource : SaturatingSourcePair B i j)
    (hsizes : ∀ k : Fin r,
      ((Finset.univ.filter fun x : VH => B.sourceCluster x = k).card = n ∨
       (Finset.univ.filter fun x : VH => B.sourceCluster x = k).card = n + 1) ∧
      (Finset.univ.filter fun x : VH => B.sourceCluster x = k).card =
        (Finset.univ.filter fun v : VG => B.hostCluster v = k).card)
    (X : Finset VH) (f : PartialCompatibleEmbedding B A X)
    (O W J : SimpleGraph (VH ⊕ VG)) :
    let U := (Finset.univ.filter fun x : VH => B.sourceCluster x = i).image
      (Sum.inl : VH → VH ⊕ VG)
    let K := (Finset.univ.filter fun v : VG => B.hostCluster v = i).image
      (Sum.inr : VG → VH ⊕ VG)
    let V := (Finset.univ.filter fun x : VH => B.sourceCluster x = j).image
      (Sum.inl : VH → VH ⊕ VG)
    let Z := (Finset.univ.filter fun v : VG => B.hostCluster v = j).image
      (Sum.inr : VG → VH ⊕ VG)
    let Aj := SimpleGraph.fromRel fun p s =>
      ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧
        (x, v) ∈ UpdatedCandidacyCluster B A X f j
    let H0 : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
      ∃ v w : VG, p = Sum.inr v ∧ s = Sum.inr w ∧ G.Adj v w
    O ≤ Aj → W ≤ O → J ≤ H0 →
    @SuperRegularPair _ _ O (Classical.decRel _) V Z
      (epsilon round) (density y) →
    @SuperRegularPair _ _ W (Classical.decRel _) V Z (xi round) (rho y) →
    ∃ F13 : SimpleGraph (VH ⊕ VG),
      @SuperRegularPair _ _ F13 (Classical.decRel _) U Z (eta round) (rho y) ∧
      (∀ sigma : U → K, Function.Bijective sigma →
        let I := @MatchingInducedGraph _ _ _ F13 J
          (Classical.decRel _) (Classical.decRel _) U K Z sigma
        let L := Finset.univ.image (Sum.inl : U → U ⊕ Z)
        let Q := Finset.univ.image (Sum.inr : Z → U ⊕ Z)
        @SuperRegularPair _ _ I (Classical.decRel _) L Q
          (omega (round + 1)) (rho y * (d / 2)) →
        let T := SimpleGraph.fromRel fun p s =>
          ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧
            (x, v) ∈ UpdatedCandidacyCluster B A X f j ∧
            ∀ u : U, (∃ z : VH, (u : VH ⊕ VG) = Sum.inl z ∧ H.Adj z x) →
              ∃ w : VG, (sigma u : VH ⊕ VG) = Sum.inr w ∧ G.Adj w v
        ∃ Wnew : SimpleGraph (VH ⊕ VG), Wnew ≤ T ∧
          @SuperRegularPair _ _ Wnew (Classical.decRel _) V Z
            (epsilon (round + 1)) (rho y * (d / 2))) := by
-- BODY
  classical
  dsimp only
  let L := fun k : Fin r =>
    (Finset.univ.filter fun x : VH => B.sourceCluster x = k).image
      (Sum.inl : VH → VH ⊕ VG)
  let Q := fun k : Fin r =>
    (Finset.univ.filter fun v : VG => B.hostCluster v = k).image
      (Sum.inr : VG → VH ⊕ VG)
  let U := L i
  let K := Q i
  let V := L j
  let Z := Q j
  let Aj := SimpleGraph.fromRel fun p s =>
    ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧
      (x, v) ∈ UpdatedCandidacyCluster B A X f j
  let H0 : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
    ∃ v w : VG, p = Sum.inr v ∧ s = Sum.inr w ∧ G.Adj v w
  intro hOA hWO hJH hO hW
  letI : DecidableRel O.Adj := Classical.decRel _
  letI : DecidableRel W.Adj := Classical.decRel _
  letI : DecidableRel J.Adj := Classical.decRel _
  let M : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
    ∃ x z : VH, p = Sum.inl x ∧ s = Sum.inl z ∧ H.Adj x z
  have adjM (x z : VH) : M.Adj (Sum.inl x) (Sum.inl z) ↔ H.Adj x z := by
    simp only [M, SimpleGraph.fromRel_adj, Sum.inl.injEq]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨x', z', rfl, rfl, hh⟩ := hh; exact hh
      · obtain ⟨x', z', rfl, rfl, hh⟩ := hh; exact hh.symm
    · intro hh
      exact ⟨fun he => H.ne_of_adj hh (Sum.inl_injective he),
        Or.inl ⟨x, z, rfl, rfl, hh⟩⟩
  let e (k : Fin r) : {x : VH // B.sourceCluster x = k} ≃ L k :=
    Equiv.ofBijective
      (fun x => ⟨Sum.inl x.val, Finset.mem_image.mpr
        ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩, rfl⟩⟩)
      ⟨by
        intro x z he
        exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val he)), by
        intro z
        obtain ⟨x, hx, he⟩ := Finset.mem_image.mp z.property
        exact ⟨⟨x, (Finset.mem_filter.mp hx).2⟩, Subtype.ext he⟩⟩
  have coeE (k : Fin r) (x : {x : VH // B.sourceCluster x = k}) :
      (e k x : VH ⊕ VG) = Sum.inl x.val := rfl
  have source :
      (∃ t : U ↪ V, ∀ u : U, ∀ v : V, M.Adj u v ↔ v = t u) ∨
      (∃ t : V ↪ U, ∀ u : U, ∀ v : V, M.Adj u v ↔ u = t v) := by
    rcases hsource with ⟨t, ht⟩ | ⟨t, ht⟩
    · let t' : U ↪ V := (e i).symm.toEmbedding.trans (t.trans (e j).toEmbedding)
      refine Or.inl ⟨t', ?_⟩
      intro u v
      have hh := ht ((e i).symm u) ((e j).symm v)
      have hm := adjM ((e i).symm u).val ((e j).symm v).val
      rw [← coeE, ← coeE, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hm
      rw [hm, hh]
      exact ⟨fun he => by simpa only [t', Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply, ← he, Equiv.apply_symm_apply],
        fun he => by
          apply (e j).injective
          simpa only [Equiv.apply_symm_apply] using he⟩
    · let t' : V ↪ U := (e j).symm.toEmbedding.trans (t.trans (e i).toEmbedding)
      refine Or.inr ⟨t', ?_⟩
      intro u v
      have hh := ht ((e i).symm u) ((e j).symm v)
      have hm := adjM ((e i).symm u).val ((e j).symm v).val
      rw [← coeE, ← coeE, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hm
      rw [hm, hh]
      exact ⟨fun he => by simpa only [t', Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply, ← he, Equiv.apply_symm_apply],
        fun he => by
          apply (e i).injective
          simpa only [Equiv.apply_symm_apply] using he⟩
  have cardL (k : Fin r) : (L k).card =
      (Finset.univ.filter fun x : VH => B.sourceCluster x = k).card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have cardQ (k : Fin r) : (Q k).card = (L k).card := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective, cardL]
    exact (hsizes k).2.symm
  have sizeU : U.card = n ∨ U.card = n + 1 := by rw [cardL]; exact (hsizes i).1
  have sizeV : V.card = n ∨ V.card = n + 1 := by rw [cardL]; exact (hsizes j).1
  have sourceHost (s t : Fin r) : Disjoint (L s) (Q t) := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzQ
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzL
    obtain ⟨v, _, he⟩ := Finset.mem_image.mp hzQ
    cases he
  have hKZ : Disjoint K Z := by
    apply Finset.disjoint_left.mpr
    intro z hzK hzZ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hzK
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hzZ
    have he' := Sum.inr_injective he
    subst w
    exact R.ne_of_adj hij
      (((Finset.mem_filter.mp hv).2).symm.trans (Finset.mem_filter.mp hw).2)
  have heta : eta round ≤ 1 := by
    have htwo : eta round ≤ 2 * eta round := by
      calc
        eta round ≤ eta round + eta round := le_add_right le_rfl
        _ = 2 * eta round := by ring
    exact htwo.trans (P.host_density_upper.le.trans tsub_le_self)
  have hp : rho y ≤ 1 :=
    (tsub_pos_iff_lt.mp ((zero_le _).trans_lt (P.witness_density y hy.le).2)).le
  have hd : d / 2 ≤ 1 :=
    (tsub_pos_iff_lt.mp ((zero_le _).trans_lt P.host_density_upper)).le
  have hph : rho y * (d / 2) ≤ 1 := by
    calc
      rho y * (d / 2) ≤ 1 * 1 := mul_le_mul' hp hd
      _ = 1 := one_mul _
  have heps : epsilon round ≤ 1 := P.error_monotone.trans P.error_unit
  have complement (A B : Finset (VH ⊕ VG)) (t : A ↪ B)
      (hcard : B.card = A.card + 1) :
      ∃ z ∈ B, ∃ tau : A ≃ B.erase z, ∀ x, (tau x : VH ⊕ VG) = (t x : VH ⊕ VG) := by
    as_aux_lemma =>
      let S := Finset.univ.image fun x : A => (t x : VH ⊕ VG)
      have hS : S ⊆ B := by
        intro x hx
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
        exact (t a).property
      have hsize : S.card = A.card := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a b he
          exact t.injective (Subtype.ext he)
      have hdiff : (B \ S).card = 1 := by
        rw [Finset.card_sdiff_of_subset hS, hsize, hcard]; omega
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiff
      have hzB : z ∈ B := (Finset.mem_sdiff.mp (hz.symm ▸ Finset.mem_singleton_self z)).1
      have hzS : z ∉ S := (Finset.mem_sdiff.mp (hz.symm ▸ Finset.mem_singleton_self z)).2
      have image : S = B.erase z := by
        ext x
        constructor
        · intro hx
          exact Finset.mem_erase.mpr ⟨fun he => hzS (he ▸ hx), hS hx⟩
        · intro hx
          obtain ⟨hne, hxB⟩ := Finset.mem_erase.mp hx
          by_contra hxS
          have hh : x ∈ B \ S := Finset.mem_sdiff.mpr ⟨hxB, hxS⟩
          rw [hz, Finset.mem_singleton] at hh
          exact hne hh
      let g : A → B.erase z := fun x => ⟨t x, image ▸
        Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
      have hg : Function.Bijective g := by
        constructor
        · intro x y he
          exact t.injective (Subtype.ext
            (congrArg (fun z : B.erase _ => (z : VH ⊕ VG)) he))
        · intro y
          have hyS : (y : VH ⊕ VG) ∈ S := image.symm ▸ y.property
          obtain ⟨x, _, he⟩ := Finset.mem_image.mp hyS
          exact ⟨x, Subtype.ext he⟩
      exact ⟨z, hzB, Equiv.ofBijective g hg, fun _ => rfl⟩
  have assembled : ∃ F13 : SimpleGraph (VH ⊕ VG),
      @SuperRegularPair _ _ F13 (Classical.decRel _) U Z (eta round) (rho y) ∧
      (∀ sigma : U → K, Function.Bijective sigma →
        let I := @MatchingInducedGraph _ _ _ F13 J (Classical.decRel _) _ U K Z sigma
        let LP := Finset.univ.image (Sum.inl : U → U ⊕ Z)
        let QP := Finset.univ.image (Sum.inr : Z → U ⊕ Z)
        @SuperRegularPair _ _ I (Classical.decRel _) LP QP
          (omega (round + 1)) (rho y * (d / 2)) →
        let Anew := SimpleGraph.fromRel fun v z =>
          v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
            ∀ u : U, M.Adj u v → H0.Adj (sigma u) z
        ∃ Wnew : SimpleGraph (VH ⊕ VG), Wnew ≤ Anew ∧
          @SuperRegularPair _ _ Wnew (Classical.decRel _) V Z
            (epsilon (round + 1)) (rho y * (d / 2))) := by
    by_cases heq : U.card = V.card
    · have equiv : ∃ tau : U ≃ V, ∀ u : U, ∀ v : V, M.Adj u v ↔ v = tau u := by
        rcases source with ⟨t, ht⟩ | ⟨t, ht⟩
        · have hb : Function.Bijective t :=
            (Fintype.bijective_iff_injective_and_card t).mpr
              ⟨t.injective, by simpa using heq⟩
          exact ⟨Equiv.ofBijective t hb, ht⟩
        · have hb : Function.Bijective t :=
            (Fintype.bijective_iff_injective_and_card t).mpr
              ⟨t.injective, by simpa using heq.symm⟩
          let tau := Equiv.ofBijective t hb
          refine ⟨tau.symm, ?_⟩
          intro u v
          rw [ht]
          exact ⟨fun he => by rw [he]; exact (tau.symm_apply_apply v).symm,
            fun he => by rw [he]; exact (tau.apply_symm_apply u).symm⟩
      obtain ⟨tau, ht⟩ := equiv
      obtain ⟨F13, hF13, _, hout⟩ := EqualSizeSourceWitnessTransport U K V Z U.card
        M O W J H0 tau (xi round) (eta round) (omega (round + 1))
        (epsilon (round + 1)) (rho y) (d / 2)
        (sourceHost i i) (sourceHost i j) hKZ (sourceHost j j)
        rfl (cardQ i) heq.symm ((cardQ j).trans heq.symm) ht hWO hJH
        P.inner_reserve.le P.output_error.le hW
      exact ⟨F13, hF13, hout⟩
    · rcases sizeU with hu | hu <;> rcases sizeV with hv | hv
      · exact False.elim (heq (hu.trans hv.symm))
      · rcases source with ⟨t, hsource'⟩ | ⟨t, hsource'⟩
        · obtain ⟨v0, hv0, tau, htau⟩ := complement U V t (by omega)
          have ht : ∀ u : U, ∀ v : V, M.Adj u v ↔ (v : VH ⊕ VG) = tau u := by
            intro u v
            rw [hsource', htau]
            exact ⟨congrArg Subtype.val, Subtype.ext⟩
          obtain ⟨F13, hF13, _, hout⟩ := FutureExtraSourceWitnessTransport
            U K V Z n v0 M O W J H0 tau (xi round) (eta round)
            (omega (round + 1)) (epsilon (round + 1)) (rho y) (d / 2)
            (epsilon round) (density y) (sourceHost i i) (sourceHost i j)
            hKZ (sourceHost j j) hv0 hn hu ((cardQ i).trans hu) hv ((cardQ j).trans hv)
            ht hWO hJH hp hph P.inner_reserve heta P.inner_degree_reserve
            P.inner_regularity_reserve P.output_error P.error_unit
            (P.outer_reserve y hy.le).1 (P.outer_reserve y hy.le).2 heps
            (by rw [← P.density_update y hy]; exact P.density_gap y hy) hO hW
          exact ⟨F13, hF13, hout⟩
        · have hh := Fintype.card_le_of_injective t t.injective
          simp only [Fintype.card_coe] at hh
          omega
      · rcases source with ⟨t, hsource'⟩ | ⟨t, hsource'⟩
        · have hh := Fintype.card_le_of_injective t t.injective
          simp only [Fintype.card_coe] at hh
          omega
        · obtain ⟨u0, hu0, tau, htau⟩ := complement V U t (by omega)
          have ht : ∀ u : U, ∀ v : V, M.Adj u v ↔ (u : VH ⊕ VG) = tau v := by
            intro u v
            rw [hsource', htau]
            exact ⟨congrArg Subtype.val, Subtype.ext⟩
          obtain ⟨F13, hF13, _, hout⟩ := CurrentExtraSourceWitnessTransport
            U K V Z n u0 M O W J H0 tau (xi round) (eta round)
            (omega (round + 1)) (epsilon (round + 1)) (rho y) (d / 2)
            (sourceHost i i) (sourceHost i j) hKZ (sourceHost j j) hu0 hn
            hu ((cardQ i).trans hu) hv ((cardQ j).trans hv) ht hWO hJH
            hp hph P.inner_reserve heta P.integer_reserve P.inner_degree_reserve
            P.inner_regularity_reserve P.output_error P.error_unit
            (P.outer_reserve y hy.le).1 (P.outer_reserve y hy.le).2 hW
          exact ⟨F13, hF13, hout⟩
      · exact False.elim (heq (hu.trans hv.symm))
  obtain ⟨F13, hF13, hout⟩ := assembled
  refine ⟨F13, hF13, ?_⟩
  intro sigma hsigma hI
  obtain ⟨Wnew, hsub, hnew⟩ := hout sigma hsigma hI
  refine ⟨Wnew, ?_, hnew⟩
  let T := SimpleGraph.fromRel fun p s =>
    ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ s = Sum.inr v ∧
      (x, v) ∈ UpdatedCandidacyCluster B A X f j ∧
      ∀ u : U, (∃ z : VH, (u : VH ⊕ VG) = Sum.inl z ∧ H.Adj z x) →
        ∃ w : VG, (sigma u : VH ⊕ VG) = Sum.inr w ∧ G.Adj w v
  change Wnew ≤ T
  have adjH (v w : VG) : H0.Adj (Sum.inr v) (Sum.inr w) ↔ G.Adj v w := by
    simp only [H0, SimpleGraph.fromRel_adj, Sum.inr.injEq]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨v', w', rfl, rfl, hh⟩ := hh; exact hh
      · obtain ⟨v', w', rfl, rfl, hh⟩ := hh; exact hh.symm
    · intro hh
      exact ⟨fun he => G.ne_of_adj hh (Sum.inr_injective he),
        Or.inl ⟨v, w, rfl, rfl, hh⟩⟩
  have forward (v z : VH ⊕ VG) (hv : v ∈ V) (hz : z ∈ Z)
      (hOvz : O.Adj v z)
      (hconstraint : ∀ u : U, M.Adj u v → H0.Adj (sigma u) z) : T.Adj v z := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    have hc : (x, w) ∈ UpdatedCandidacyCluster B A X f j := by
      have hh := hOA hOvz
      obtain ⟨_, hh | hh⟩ := hh
      · obtain ⟨x', w', hx', hw', hc⟩ := hh
        cases Sum.inl_injective hx'
        cases Sum.inr_injective hw'
        exact hc
      · obtain ⟨x', w', hx', _, _⟩ := hh
        cases hx'
    refine ⟨by simp, Or.inl ⟨x, w, rfl, rfl, hc, ?_⟩⟩
    intro u hu
    obtain ⟨z, hz, hzx⟩ := hu
    have hm : M.Adj u (Sum.inl x) := by rw [hz]; exact (adjM z x).mpr hzx
    have hh := hconstraint u hm
    obtain ⟨v, _, he⟩ := Finset.mem_image.mp (sigma u).property
    exact ⟨v, he.symm, (adjH v w).mp (he ▸ hh)⟩
  intro v z hvz
  obtain ⟨_, hh | hh⟩ := hsub hvz
  · exact forward v z hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  · exact (forward z v hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
