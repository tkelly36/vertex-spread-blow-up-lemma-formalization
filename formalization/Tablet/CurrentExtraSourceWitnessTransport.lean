import Tablet.MatchingInducedUpdatedCandidacyTransport
import Tablet.MatchingInducedLeftRowDeletion
import Tablet.FutureExtraVertexStability

-- [TABLET NODE: CurrentExtraSourceWitnessTransport]
theorem CurrentExtraSourceWitnessTransport
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (U K V Z : Finset (S ⊕ T)) (n : ℕ) (u0 : S ⊕ T)
    (M O W J H : SimpleGraph (S ⊕ T))
    [DecidableRel W.Adj] [DecidableRel J.Adj]
    (tau : V ≃ (U.erase u0)) (xi eta omega eps p h : ENNReal)
    (hUK : Disjoint U K) (hUZ : Disjoint U Z) (hKZ : Disjoint K Z)
    (hVZ : Disjoint V Z) (hu0 : u0 ∈ U)
    (hn : 1 ≤ n) (hU : U.card = n + 1) (hK : K.card = n + 1)
    (hV : V.card = n) (hZ : Z.card = n)
    (hM : ∀ u : U, ∀ v : V, M.Adj u v ↔ (u : S ⊕ T) = tau v)
    (hWO : W ≤ O) (hJH : J ≤ H)
    (hp : p ≤ 1) (hph : p * h ≤ 1)
    (hxi : xi < eta) (heta : eta ≤ 1) (hinteger : (n : ENNReal)⁻¹ ≤ xi)
    (hinner : xi + 2 / (n : ENNReal) ≤ eta)
    (hinnerReg : xi + 1 / (eta * (n : ENNReal)) ≤ eta)
    (homega : omega < eps) (heps : eps ≤ 1)
    (houter : omega + 2 / (n : ENNReal) ≤ eps)
    (houterReg : omega + 1 / (eps * (n : ENNReal)) ≤ eps)
    (hW : SuperRegularPair W V Z xi p) :
    ∃ F : SimpleGraph (S ⊕ T),
      @SuperRegularPair (S ⊕ T) _ F (Classical.decRel _) U Z eta p ∧
      (∀ v : V, ∀ z : Z, F.Adj (tau v) z ↔ W.Adj v z) ∧
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
  -- Relabelling preserves every rectangle and both neighbourhood cardinalities.
  have relabel : ∀ {A B : Type _} [DecidableEq A] [DecidableEq B]
      (G : SimpleGraph A) (D : SimpleGraph B)
      [DecidableRel G.Adj] [DecidableRel D.Adj]
      (L R : Finset A) (L' R' : Finset B) (f : A → B) (e d : ENNReal),
      Set.InjOn f L → Set.InjOn f R → L.image f = L' → R.image f = R' →
      (∀ x ∈ L, ∀ z ∈ R, G.Adj x z ↔ D.Adj (f x) (f z)) →
      SuperRegularPair G L R e d → SuperRegularPair D L' R' e d := by
    intro A B _ _ G D _ _ L R L' R' f e d injL injR imageL imageR adj hG
    have cardL : L'.card = L.card := by
      rw [← imageL]
      exact Finset.card_image_iff.mpr injL
    have cardR : R'.card = R.card := by
      rw [← imageR]
      exact Finset.card_image_iff.mpr injR
    have pull : ∀ (P Q : Finset A) (X : Finset B),
        Q = P.filter (fun x => f x ∈ X) → X ⊆ P.image f → Q.image f = X := by
      intro P Q X hQ hX
      subst Q
      ext x
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨y, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hX hx)
        exact ⟨y, ⟨hy, hx⟩, rfl⟩
    have edges : ∀ X ⊆ L, ∀ Y ⊆ R,
        ((X.product Y).filter fun q => G.Adj q.1 q.2).card =
        (((X.image f).product (Y.image f)).filter fun q => D.Adj q.1 q.2).card := by
      intro X hX Y hY
      apply Finset.card_bij (fun q _ => (f q.1, f q.2))
      · intro q hq
        obtain ⟨hq, ha⟩ := Finset.mem_filter.mp hq
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨q.1, hx, rfl⟩,
           Finset.mem_image.mpr ⟨q.2, hy, rfl⟩⟩,
          (adj _ (hX hx) _ (hY hy)).mp ha⟩
      · intro q hq r hr he
        have hq' := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
        have hr' := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
        exact Prod.ext (injL (hX hq'.1) (hX hr'.1) (congrArg Prod.fst he))
          (injR (hY hq'.2) (hY hr'.2) (congrArg Prod.snd he))
      · intro q hq
        obtain ⟨hq, ha⟩ := Finset.mem_filter.mp hq
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
        obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hx
        obtain ⟨y, hy, hf⟩ := Finset.mem_image.mp hy
        refine ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩,
          Prod.ext he hf⟩
        exact (adj _ (hX hx) _ (hY hy)).mpr (by simpa only [he, hf] using ha)
    have counts : ∀ (P : Finset A) (hinj : Set.InjOn f P)
        (a : A → Prop) (b : B → Prop) [DecidablePred a] [DecidablePred b],
        (∀ x ∈ P, a x ↔ b (f x)) →
        (P.filter a).card = ((P.image f).filter b).card := by
      intro P hinj a b _ _ hab
      apply Finset.card_bij (fun x _ => f x)
      · intro x hx
        obtain ⟨hx, ha⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, (hab x hx).mp ha⟩
      · intro x hx y hy he
        exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
      · intro y hy
        obtain ⟨hy, hb⟩ := Finset.mem_filter.mp hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, (hab x hx).mpr hb⟩, rfl⟩
    rcases hG with ⟨hr, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hx hy
      let X0 := L.filter (fun x => f x ∈ X)
      let Y0 := R.filter (fun y => f y ∈ Y)
      have hX0 : X0 ⊆ L := Finset.filter_subset _ _
      have hY0 : Y0 ⊆ R := Finset.filter_subset _ _
      have imX : X0.image f = X := pull L X0 X rfl (by simpa only [imageL] using hX)
      have imY : Y0.image f = Y := pull R Y0 Y rfl (by simpa only [imageR] using hY)
      have cx : X.card = X0.card := by
        rw [← imX]
        exact Finset.card_image_iff.mpr (injL.mono hX0)
      have cy : Y.card = Y0.card := by
        rw [← imY]
        exact Finset.card_image_iff.mpr (injR.mono hY0)
      have density : PairDensity G X0 Y0 = PairDensity D X Y := by
        unfold PairDensity
        rw [edges X0 hX0 Y0 hY0, imX, imY, cx, cy]
      rw [cardL, cx] at hx
      rw [cardR, cy] at hy
      simpa only [density] using hr X0 hX0 Y0 hY0 hx hy
    · intro x hx
      rw [← imageL] at hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      have hc := counts R injR (fun z => G.Adj u z) (fun z => D.Adj (f u) z)
        (fun z hz => adj u hu z hz)
      rw [imageR] at hc
      simpa only [cardR, ← hc] using hl u hu
    · intro z hz
      rw [← imageR] at hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hc := counts L injL (fun x => G.Adj x w) (fun x => D.Adj x (f w))
        (fun x hx => adj x hx w hw)
      rw [imageL] at hc
      simpa only [cardL, ← hc] using hh w hw
  let U0 := U.erase u0
  have hU0 : U0.card = n := by
    simp only [U0, Finset.card_erase_of_mem hu0, hU, Nat.add_sub_cancel]
  have hU0Z : Disjoint U0 Z := hUZ.mono_left (Finset.erase_subset _ _)
  have hu0Z : u0 ∉ Z := Finset.disjoint_left.mp hUZ hu0
  let G : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun x z =>
    ∃ v : V, ∃ w : Z, x = tau v ∧ z = w ∧ W.Adj v w
  letI : DecidableRel G.Adj := Classical.decRel _
  have adjG : ∀ v : V, ∀ z : Z, G.Adj (tau v) z ↔ W.Adj v z := by
    intro v z
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨v', w, hv, hw, ha⟩ := hh
        have he : v = v' := tau.injective (Subtype.ext hv)
        have hz : z = w := Subtype.ext hw
        simpa only [he, hz] using ha
      · obtain ⟨v', w, hv, hw, _⟩ := hh
        exact False.elim (Finset.disjoint_left.mp hU0Z (tau v').property (hv ▸ z.property))
    · intro ha
      refine ⟨?_, Or.inl ⟨v, z, rfl, rfl, ha⟩⟩
      intro he
      exact Finset.disjoint_left.mp hU0Z (tau v).property (he ▸ z.property)
  let f : S ⊕ T → S ⊕ T := fun x => if hx : x ∈ V then tau ⟨x, hx⟩ else x
  have fe : ∀ v : V, f v = tau v := by intro v; simp [f, v.property]
  have fz : ∀ z ∈ Z, f z = z := by
    intro z hz
    have hv : z ∉ V := fun hv => Finset.disjoint_left.mp hVZ hv hz
    simp only [f, dif_neg hv]
  have injV : Set.InjOn f V := by
    intro x hx y hy he
    have hh : tau ⟨x, hx⟩ = tau ⟨y, hy⟩ := Subtype.ext
      (by simpa only [← fe ⟨x, hx⟩, ← fe ⟨y, hy⟩] using he)
    exact congrArg Subtype.val (tau.injective hh)
  have injZ : Set.InjOn f Z := by
    intro x hx y hy he
    simpa only [fz x hx, fz y hy] using he
  have imV : V.image f = U0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      rw [fe ⟨v, hv⟩]
      exact (tau ⟨v, hv⟩).property
    · intro hx
      obtain ⟨v, he⟩ := tau.surjective ⟨x, hx⟩
      exact Finset.mem_image.mpr ⟨v, v.property, (fe v).trans (congrArg Subtype.val he)⟩
  have imZ : Z.image f = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa only [fz w hw] using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨z, hz, fz z hz⟩
  have hG : SuperRegularPair G U0 Z xi p := by
    apply relabel W G V Z U0 Z f xi p injV injZ imV imZ
    · intro v hv z hz
      simpa only [fe ⟨v, hv⟩, fz z hz] using (adjG ⟨v, hv⟩ ⟨z, hz⟩).symm
    · exact hW
  -- The floor row is available in an auxiliary ambient graph only.
  have hnt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpFinite : p ≠ ⊤ := ne_of_lt (hp.trans_lt ENNReal.one_lt_top)
  have hpnFinite : p * (n : ENNReal) ≠ ⊤ := ENNReal.mul_ne_top hpFinite hnt
  let k : ℕ := ⌊(p * (n : ENNReal)).toReal⌋₊
  have hk : (k : ENNReal) ≤ p * (n : ENNReal) := by
    have hh := ENNReal.ofReal_le_ofReal
      (Nat.floor_le (ENNReal.toReal_nonneg : 0 ≤ (p * (n : ENNReal)).toReal))
    simpa only [k, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hpnFinite] using hh
  have hkRound : p * (n : ENNReal) ≤ (k : ENNReal) + 1 := by
    have hh := ENNReal.ofReal_le_ofReal
      (Nat.lt_floor_add_one (p * (n : ENNReal)).toReal).le
    simpa only [k, ENNReal.ofReal_toReal hpnFinite,
      ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh
  have hreserve : (1 : ENNReal) ≤ eta * (n : ENNReal) := by
    calc
      1 = (1 / (n : ENNReal)) * n := (ENNReal.div_mul_cancel hn0 hnt).symm
      _ ≤ eta * n := mul_le_mul_left (by simpa only [one_div] using hinteger.trans hxi.le) _
  have hkLower : (p - eta) * (Z.card : ENNReal) ≤ k := by
    rw [hZ, ENNReal.sub_mul (fun _ _ => hnt), tsub_le_iff_right]
    exact hkRound.trans (add_le_add le_rfl hreserve)
  have hkUpper : (k : ENNReal) ≤ (p + eta) * (Z.card : ENNReal) := by
    rw [hZ]
    exact hk.trans (mul_le_mul_left (le_add_right le_rfl) _)
  have hkn : k ≤ Z.card := by
    rw [hZ]
    have hh : (k : ENNReal) ≤ (n : ENNReal) :=
      hk.trans (by simpa only [one_mul] using mul_le_mul_left hp (n : ENNReal))
    exact_mod_cast hh
  obtain ⟨N, hNZ, hNk⟩ := Finset.exists_subset_card_eq hkn
  let D : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun x z =>
    (∃ v : V, ∃ w : Z, x = tau v ∧ z = w ∧ W.Adj v w) ∨ (x = u0 ∧ z ∈ N)
  letI : DecidableRel D.Adj := Classical.decRel _
  have hGD : G ≤ D := by
    intro x z hxz
    rw [SimpleGraph.fromRel_adj] at hxz ⊢
    exact ⟨hxz.1, hxz.2.elim (fun hh => Or.inl (Or.inl hh))
      (fun hh => Or.inr (Or.inl hh))⟩
  have rowD : ∀ z ∈ Z, D.Adj u0 z ↔ z ∈ N := by
    intro z hz
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, (hh | hh) | (hh | hh)⟩
      · obtain ⟨v, w, hv, _, _⟩ := hh
        exact False.elim ((Finset.mem_erase.mp (tau v).property).1 hv.symm)
      · exact hh.2
      · obtain ⟨v, w, _, hw, _⟩ := hh
        exact False.elim (hu0Z (hw ▸ w.property))
      · exact False.elim (hu0Z (hh.1 ▸ hz))
    · intro hzN
      refine ⟨?_, Or.inl (Or.inr ⟨rfl, hzN⟩)⟩
      intro he
      exact hu0Z (he ▸ hz)
  have rowCount : (Z.filter fun z => D.Adj u0 z).card = k := by
    have he : (Z.filter fun z => D.Adj u0 z) = N := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun hz => (rowD z hz.1).mp hz.2,
        fun hz => ⟨hNZ hz, (rowD z (hNZ hz)).mpr hz⟩⟩
    rw [he, hNk]
  obtain ⟨N', F, _, _, _, _, _, haway, hF⟩ :=
    FutureExtraVertexStability n k xi eta p hn hxi heta hp hinner hinnerReg G D U0 Z u0
      hU0Z (Finset.notMem_erase _ _) hu0Z hU0 (Or.inl hZ) hGD
      (by rw [rowCount]) hkLower hkUpper hG
  letI : DecidableRel F.Adj := Classical.decRel _
  have adjF : ∀ v : V, ∀ z : Z, F.Adj (tau v) z ↔ W.Adj v z := by
    intro v z
    exact (haway _ _ (Finset.mem_erase.mp (tau v).property).1
      (fun he => hu0Z (he ▸ z.property))).trans (adjG v z)
  refine ⟨F, ?_, adjF, ?_⟩
  · simpa only [U0, Finset.insert_erase hu0] using hF
  intro sigma hsigma
  dsimp only
  intro hI
  let I := @MatchingInducedGraph (S ⊕ T) _ _ F J (Classical.decRel _) _ U K Z sigma
  letI : DecidableRel I.Adj := Classical.decRel _
  let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
  let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
  let a : U := ⟨u0, hu0⟩
  let L0 := L.erase (Sum.inl a)
  have disjLR : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    obtain ⟨u, _, he⟩ := Finset.mem_image.mp hq
    obtain ⟨z, _, hf⟩ := Finset.mem_image.mp hr
    exact Sum.inl_ne_inr (he.trans hf.symm)
  have haL : Sum.inl a ∈ L := by simp [L]
  have cardL : L.card = n + 1 := by
    rw [Finset.card_image_iff.mpr (by intro x _ y _ he; exact Sum.inl.inj he)]
    simpa only [Finset.card_univ, Fintype.card_coe] using hU
  have cardR : R.card = n := by
    rw [Finset.card_image_iff.mpr (by intro x _ y _ he; exact Sum.inr.inj he)]
    simpa only [Finset.card_univ, Fintype.card_coe] using hZ
  have hdeleted : SuperRegularPair I L0 R eps (p * h) :=
    MatchingInducedLeftRowDeletion n omega eps (p * h) hn homega heps hph
      houter houterReg I L R (Sum.inl a) disjLR haL cardL (Or.inl cardR) hI
  let up : U0 → U := fun u => ⟨u, Finset.mem_of_mem_erase u.property⟩
  have left : ∀ q ∈ L0, ∃ u : U0, q = Sum.inl (up u) := by
    intro q hq
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hq
    have hu : (u : S ⊕ T) ≠ u0 := by
      intro he
      exact hne (congrArg Sum.inl (Subtype.ext he))
    exact ⟨⟨u, Finset.mem_erase.mpr ⟨hu, u.property⟩⟩, rfl⟩
  have inLeft : ∀ u : U0, Sum.inl (up u) ∈ L0 := by
    intro u
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro he
      exact (Finset.mem_erase.mp u.property).1 (congrArg Subtype.val (Sum.inl.inj he))
    · simp [L]
  have right : ∀ q ∈ R, ∃ z : Z, q = Sum.inr z := by
    intro q hq
    obtain ⟨z, _, he⟩ := Finset.mem_image.mp hq
    exact ⟨z, he.symm⟩
  let Wnew : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun v z =>
    ∃ u : U0, ∃ w : Z, v = tau.symm u ∧ z = w ∧
      F.Adj u w ∧ J.Adj (sigma (up u)) w
  letI : DecidableRel Wnew.Adj := Classical.decRel _
  have adjNew : ∀ u : U0, ∀ z : Z,
      Wnew.Adj (tau.symm u) z ↔ F.Adj u z ∧ J.Adj (sigma (up u)) z := by
    intro u z
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨u', w, hu, hw, ha⟩ := hh
        have he : u = u' := tau.symm.injective (Subtype.ext hu)
        have hz : z = w := Subtype.ext hw
        simpa only [he, hz] using ha
      · obtain ⟨u', w, hv, _, _⟩ := hh
        exact False.elim (Finset.disjoint_left.mp hVZ (tau.symm u').property (hv ▸ z.property))
    · intro ha
      refine ⟨?_, Or.inl ⟨u, z, rfl, rfl, ha⟩⟩
      intro he
      exact Finset.disjoint_left.mp hVZ (tau.symm u).property (he ▸ z.property)
  let g : U ⊕ Z → S ⊕ T := Sum.elim
    (fun u => if hu : (u : S ⊕ T) ∈ U0 then tau.symm ⟨u, hu⟩ else u) Subtype.val
  have gu : ∀ u : U0, g (Sum.inl (up u)) = tau.symm u := by
    intro u
    simp only [g, Sum.elim_inl, up, u.property, dif_pos]
    apply congrArg (fun u : U0 => (tau.symm u).val)
    exact Subtype.ext rfl
  have gz : ∀ z : Z, g (Sum.inr z) = z := by intro z; rfl
  have injL0 : Set.InjOn g L0 := by
    intro q hq r hr he
    obtain ⟨u, rfl⟩ := left q hq
    obtain ⟨v, rfl⟩ := left r hr
    have huv : u = v := tau.symm.injective (Subtype.ext (by simpa only [gu] using he))
    exact congrArg (fun u => Sum.inl (up u)) huv
  have injR : Set.InjOn g R := by
    intro q hq r hr he
    obtain ⟨z, rfl⟩ := right q hq
    obtain ⟨w, rfl⟩ := right r hr
    exact congrArg Sum.inr (Subtype.ext he)
  have imageL0 : L0.image g = V := by
    ext v
    constructor
    · intro hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨u, rfl⟩ := left q hq
      rw [gu]
      exact (tau.symm u).property
    · intro hv
      obtain ⟨u, he⟩ := tau.symm.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨Sum.inl (up u), inLeft u,
        (gu u).trans (congrArg Subtype.val he)⟩
  have imageR : R.image g = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨w, rfl⟩ := right q hq
      exact w.property
    · intro hz
      exact Finset.mem_image.mpr ⟨Sum.inr ⟨z, hz⟩, by simp [R], rfl⟩
  have adjI : ∀ u : U, ∀ z : Z,
      I.Adj (Sum.inl u) (Sum.inr z) ↔ F.Adj u z ∧ J.Adj (sigma u) z := by
    intro u z
    simp only [I, MatchingInducedGraph, SimpleGraph.fromRel_adj,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inl.injEq, Sum.inr.injEq,
      false_and, exists_false, or_false]
    constructor
    · rintro ⟨_, x, w, rfl, rfl, ha⟩
      exact ha
    · intro ha
      refine ⟨?_, u, z, rfl, rfl, ha⟩
      intro he
      cases he
  have hnew : SuperRegularPair Wnew V Z eps (p * h) := by
    apply relabel I Wnew L0 R V Z g eps (p * h) injL0 injR imageL0 imageR
    · intro q hq r hr
      obtain ⟨u, rfl⟩ := left q hq
      obtain ⟨z, rfl⟩ := right r hr
      rw [gu, gz, adjNew, adjI]
    · exact hdeleted
  refine ⟨Wnew, ?_, hnew⟩
  intro v z hvz
  rw [SimpleGraph.fromRel_adj] at hvz ⊢
  refine ⟨hvz.1, ?_⟩
  have forward : ∀ v z : S ⊕ T,
      (∃ u : U0, ∃ w : Z, v = tau.symm u ∧ z = w ∧
        F.Adj u w ∧ J.Adj (sigma (up u)) w) →
      v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
        ∀ x : U, M.Adj x v → H.Adj (sigma x) z := by
    rintro v z ⟨u, w, rfl, rfl, hfu, hju⟩
    have genuine : W.Adj (tau.symm u) w := by
      apply (adjF (tau.symm u) w).mp
      simpa only [tau.apply_symm_apply] using hfu
    refine ⟨(tau.symm u).property, w.property, hWO genuine, ?_⟩
    intro x hm
    have he : x = up u := Subtype.ext (by
      simpa only [tau.apply_symm_apply] using (hM x (tau.symm u)).mp hm)
    simpa only [he] using hJH hju
  exact hvz.2.elim (fun hh => Or.inl (forward v z hh))
    (fun hh => Or.inr (forward z v hh))
