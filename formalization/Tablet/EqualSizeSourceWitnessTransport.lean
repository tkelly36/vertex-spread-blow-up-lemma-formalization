import Tablet.MatchingInducedUpdatedCandidacyTransport

-- [TABLET NODE: EqualSizeSourceWitnessTransport]
theorem EqualSizeSourceWitnessTransport
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (U K V Z : Finset (S ⊕ T)) (m : ℕ)
    (M O W J H : SimpleGraph (S ⊕ T))
    [DecidableRel W.Adj] [DecidableRel J.Adj]
    (tau : U ≃ V) (xi eta omega eps p h : ENNReal)
    (hUK : Disjoint U K) (hUZ : Disjoint U Z) (hKZ : Disjoint K Z)
    (hVZ : Disjoint V Z)
    (hU : U.card = m) (hK : K.card = m) (hV : V.card = m) (hZ : Z.card = m)
    (hM : ∀ u : U, ∀ v : V, M.Adj u v ↔ v = tau u)
    (hWO : W ≤ O) (hJH : J ≤ H)
    (hxi : xi ≤ eta) (homega : omega ≤ eps)
    (hW : SuperRegularPair W V Z xi p) :
    ∃ F : SimpleGraph (S ⊕ T),
      @SuperRegularPair (S ⊕ T) _ F (Classical.decRel _) U Z eta p ∧
      (∀ u : U, ∀ z : Z, F.Adj u z ↔ W.Adj (tau u) z) ∧
      (∀ sigma : U → K, Function.Bijective sigma →
        let I := @MatchingInducedGraph (S ⊕ T) _ _ F J (Classical.decRel _) _ U K Z sigma
        let L := Finset.univ.image (Sum.inl : U → U ⊕ Z)
        let R := Finset.univ.image (Sum.inr : Z → U ⊕ Z)
        @SuperRegularPair (U ⊕ Z) _ I (Classical.decRel _) L R omega (p * h) →
        let Anew := SimpleGraph.fromRel fun v z =>
          v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
            ∀ u : U, M.Adj u v → H.Adj (sigma u) z
        ∃ Wnew : SimpleGraph (S ⊕ T), Wnew ≤ Anew ∧
          @SuperRegularPair (S ⊕ T) _ Wnew (Classical.decRel _) V Z eps (p * h)) := by
-- BODY
  classical
  have enlarge : ∀ (G : SimpleGraph (S ⊕ T)) (P Q : Finset (S ⊕ T))
      (a b d : ENNReal), a ≤ b →
      @SuperRegularPair _ _ G (Classical.decRel _) P Q a d →
      @SuperRegularPair _ _ G (Classical.decRel _) P Q b d := by
    intro G P Q a b d hab hG
    rcases hG with ⟨hr, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hx hy
      obtain ⟨lo, hi⟩ := hr X hX Y hY
        (lt_of_le_of_lt (mul_le_mul_left hab _) hx)
        (lt_of_le_of_lt (mul_le_mul_left hab _) hy)
      exact ⟨(tsub_le_tsub_left hab d).trans lo, hi.trans (add_le_add_right hab d)⟩
    · intro x hx
      exact ⟨(mul_le_mul_left (tsub_le_tsub_left hab d) _).trans (hl x hx).1,
        (hl x hx).2.trans (mul_le_mul_left (add_le_add_right hab d) _)⟩
    · intro y hy
      exact ⟨(mul_le_mul_left (tsub_le_tsub_left hab d) _).trans (hh y hy).1,
        (hh y hy).2.trans (mul_le_mul_left (add_le_add_right hab d) _)⟩
  let F : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun x z =>
    ∃ u : U, ∃ w : Z, x = u ∧ z = w ∧ W.Adj (tau u) w
  letI : DecidableRel F.Adj := Classical.decRel _
  have adjF : ∀ u : U, ∀ z : Z, F.Adj u z ↔ W.Adj (tau u) z := by
    intro u z
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨v, w, hv, hw, ha⟩ := hh
        have huv : u = v := Subtype.ext hv
        have hzw : z = w := Subtype.ext hw
        simpa only [huv, hzw] using ha
      · obtain ⟨v, w, hv, hw, _⟩ := hh
        exact False.elim (Finset.disjoint_left.mp hUZ v.property (hv ▸ z.property))
    · intro ha
      refine ⟨?_, Or.inl ⟨u, z, rfl, rfl, ha⟩⟩
      intro he
      exact Finset.disjoint_left.mp hUZ u.property (he ▸ z.property)
  let f : S ⊕ T → S ⊕ T := fun x => if hx : x ∈ U then tau ⟨x, hx⟩ else x
  have fe : ∀ u : U, f u = tau u := by intro u; simp [f, u.property]
  have finj : Set.InjOn f U := by
    intro x hx y hy he
    have he' : tau ⟨x, hx⟩ = tau ⟨y, hy⟩ :=
      Subtype.ext (by simpa only [← fe ⟨x, hx⟩, ← fe ⟨y, hy⟩] using he)
    exact congrArg Subtype.val (tau.injective he')
  have imageU : U.image f = V := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      rw [fe ⟨u, hu⟩]
      exact (tau ⟨u, hu⟩).property
    · intro hv
      obtain ⟨u, he⟩ := tau.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨u, u.property, (fe u).trans (congrArg Subtype.val he)⟩
  have cardU : V.card = U.card := by
    rw [← imageU]
    exact Finset.card_image_iff.mpr finj
  have adj : ∀ x ∈ U, ∀ z ∈ Z, F.Adj x z ↔ W.Adj (f x) z := by
    intro x hx z hz
    simpa only [fe ⟨x, hx⟩] using adjF ⟨x, hx⟩ ⟨z, hz⟩
  have counts : ∀ (P : Finset (S ⊕ T)) (g : S ⊕ T → S ⊕ T)
      (hinj : Set.InjOn g P) (a b : S ⊕ T → Prop)
      [DecidablePred a] [DecidablePred b],
      (∀ x ∈ P, a x ↔ b (g x)) →
      (P.filter a).card = ((P.image g).filter b).card := by
    intro P g hinj a b _ _ hab
    apply Finset.card_bij (fun x _ => g x)
    · intro x hx
      obtain ⟨hx, ha⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, (hab x hx).mp ha⟩
    · intro x hx y hy he
      exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
    · intro y hy
      obtain ⟨hy, hb⟩ := Finset.mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, (hab x hx).mpr hb⟩, rfl⟩
  have edges : ∀ X ⊆ U, ∀ Y ⊆ Z,
      ((X.product Y).filter fun q => F.Adj q.1 q.2).card =
      (((X.image f).product Y).filter fun q => W.Adj q.1 q.2).card := by
    intro X hX Y hY
    apply Finset.card_bij (fun q _ => (f q.1, q.2))
    · intro q hq
      obtain ⟨hq, ha⟩ := Finset.mem_filter.mp hq
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q.1, hx, rfl⟩, hy⟩, (adj _ (hX hx) _ (hY hy)).mp ha⟩
    · intro q hq r hr he
      have hq' := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hr' := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
      have he2 := congrArg Prod.snd he
      exact Prod.ext (finj (hX hq'.1) (hX hr'.1) (congrArg Prod.fst he))
        he2
    · intro q hq
      obtain ⟨hq, ha⟩ := Finset.mem_filter.mp hq
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hx
      refine ⟨(x, q.2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩,
        Prod.ext he rfl⟩
      exact (adj _ (hX hx) _ (hY hy)).mpr (by simpa only [he] using ha)
  have hF : @SuperRegularPair _ _ F (Classical.decRel _) U Z xi p := by
    rcases hW with ⟨hr, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hx hy
      have cx : (X.image f).card = X.card := Finset.card_image_iff.mpr (finj.mono hX)
      have hXV : X.image f ⊆ V := by
        rw [← imageU]
        exact Finset.image_mono f hX
      have density : PairDensity F X Y = PairDensity W (X.image f) Y := by
        unfold PairDensity
        rw [edges X hX Y hY, cx]
      rw [density]
      exact hr _ hXV Y hY (by simpa only [cardU, cx] using hx) hy
    · intro x hx
      have hc : (Z.filter fun z => F.Adj x z).card =
          (Z.filter fun z => W.Adj (f x) z).card := by
        congr 1
        ext z
        simp only [Finset.mem_filter]
        exact and_congr_right (fun hz => adj x hx z hz)
      have hf : f x ∈ V := by rw [← imageU]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      simpa only [hc] using hl _ hf
    · intro z hz
      have hc := counts U f finj (fun x => F.Adj x z) (fun x => W.Adj x z)
        (fun x hx => adj x hx z hz)
      rw [imageU] at hc
      simpa only [cardU, ← hc] using hh z hz
  refine ⟨F, enlarge F U Z xi eta p hxi hF, adjF, ?_⟩
  intro sigma hsigma
  dsimp only
  intro hI
  let Wnew : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun v z =>
    ∃ u : U, ∃ w : Z, v = tau u ∧ z = w ∧ F.Adj u w ∧ J.Adj (sigma u) w
  letI : DecidableRel Wnew.Adj := Classical.decRel _
  have adjNew : ∀ u : U, ∀ z : Z,
      Wnew.Adj (tau u) z ↔ F.Adj u z ∧ J.Adj (sigma u) z := by
    intro u z
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨v, w, hv, hw, ha⟩ := hh
        have huv : u = v := tau.injective (Subtype.ext hv)
        have hzw : z = w := Subtype.ext hw
        simpa only [huv, hzw] using ha
      · obtain ⟨v, w, hv, hw, _⟩ := hh
        exact False.elim (Finset.disjoint_left.mp hVZ (tau v).property (hv ▸ z.property))
    · intro ha
      refine ⟨?_, Or.inl ⟨u, z, rfl, rfl, ha⟩⟩
      intro he
      exact Finset.disjoint_left.mp hVZ (tau u).property (he ▸ z.property)
  let B := SimpleGraph.fromRel fun x y => x ∈ U ∧ y ∈ K
  have hB : PerfectMatching B U K hUK sigma := by
    refine ⟨hsigma, ?_⟩
    intro u
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨u.property, (sigma u).property⟩⟩
    intro he
    exact Finset.disjoint_left.mp hUK u.property (he ▸ (sigma u).property)
  have partV : ∀ v : S ⊕ T, v ∈ V ↔ ∃ u : U, v = tau u := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, he⟩ := tau.surjective ⟨v, hv⟩
      exact ⟨u, (congrArg Subtype.val he).symm⟩
    · rintro ⟨u, rfl⟩
      exact (tau u).property
  have partZ : ∀ z : S ⊕ T, z ∈ Z ↔ ∃ w : Z, z = w := by
    intro z
    exact ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, by rintro ⟨w, rfl⟩; exact w.property⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  have transported := MatchingInducedUpdatedCandidacyTransport U V K Z tau sigma
    M B F J Wnew V Z omega (p * h) hUK hB hM adjNew partV partZ hI
  refine ⟨Wnew, ?_, enlarge Wnew V Z omega eps (p * h) homega transported⟩
  intro v z hvz
  rw [SimpleGraph.fromRel_adj] at hvz ⊢
  refine ⟨hvz.1, ?_⟩
  have forward : ∀ (v z : S ⊕ T),
      (∃ u : U, ∃ w : Z, v = tau u ∧ z = w ∧ F.Adj u w ∧ J.Adj (sigma u) w) →
      v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
        ∀ u : U, M.Adj u v → H.Adj (sigma u) z := by
    rintro v z ⟨u, w, rfl, rfl, hfu, hju⟩
    refine ⟨(tau u).property, w.property, hWO ((adjF u w).mp hfu), ?_⟩
    intro u' hm
    have he : u = u' := tau.injective ((hM u' (tau u)).mp hm)
    simpa only [he] using hJH hju
  exact hvz.2.elim (fun hh => Or.inl (forward v z hh))
    (fun hh => Or.inr (forward z v hh))
