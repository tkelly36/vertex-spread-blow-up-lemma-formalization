import Tablet.MatchingInducedUpdatedCandidacyTransport
import Tablet.MatchingInducedLeftRowDeletion
import Tablet.FutureExtraVertexStability

-- [TABLET NODE: FutureExtraSourceWitnessTransport]
theorem FutureExtraSourceWitnessTransport
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (U K V Z : Finset (S ⊕ T)) (n : ℕ) (v0 : S ⊕ T)
    (M O W J H : SimpleGraph (S ⊕ T))
    [DecidableRel O.Adj] [DecidableRel W.Adj] [DecidableRel J.Adj]
    (tau : U ≃ (V.erase v0)) (xi eta omega eps p h eOld pOld : ENNReal)
    (hUK : Disjoint U K) (hUZ : Disjoint U Z) (hKZ : Disjoint K Z)
    (hVZ : Disjoint V Z) (hv0 : v0 ∈ V)
    (hn : 1 ≤ n) (hU : U.card = n) (hK : K.card = n)
    (hV : V.card = n + 1) (hZ : Z.card = n + 1)
    (hM : ∀ u : U, ∀ v : V, M.Adj u v ↔ (v : S ⊕ T) = tau u)
    (hWO : W ≤ O) (hJH : J ≤ H)
    (hp : p ≤ 1) (hph : p * h ≤ 1)
    (hxi : xi < eta) (heta : eta ≤ 1)
    (hinner : xi + 2 / (n : ENNReal) ≤ eta)
    (hinnerReg : xi + 1 / (eta * (n : ENNReal)) ≤ eta)
    (homega : omega < eps) (heps : eps ≤ 1)
    (houter : omega + 2 / (n : ENNReal) ≤ eps)
    (houterReg : omega + 1 / (eps * (n : ENNReal)) ≤ eps)
    (heOld : eOld ≤ 1)
    (hgap : p * h + eOld + 1 / (n : ENNReal) ≤ pOld)
    (hO : SuperRegularPair O V Z eOld pOld)
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
  have hres := MatchingInducedLeftRowDeletion n xi eta p hn hxi heta hp
    hinner hinnerReg W V Z v0 hVZ hv0 hV (Or.inr hZ) hW
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
  have imageU : U.image f = V.erase v0 := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      rw [fe ⟨u, hu⟩]
      exact (tau ⟨u, hu⟩).property
    · intro hv
      obtain ⟨u, he⟩ := tau.surjective ⟨v, hv⟩
      exact Finset.mem_image.mpr ⟨u, u.property, (fe u).trans (congrArg Subtype.val he)⟩
  have cardU : (V.erase v0).card = U.card := by
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
  have hF : @SuperRegularPair _ _ F (Classical.decRel _) U Z eta p := by
    rcases hres with ⟨hr, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hx hy
      have cx : (X.image f).card = X.card := Finset.card_image_iff.mpr (finj.mono hX)
      have hXV : X.image f ⊆ V.erase v0 := by
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
      have hf : f x ∈ V.erase v0 := by
        rw [← imageU]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      simpa only [hc] using hl _ hf
    · intro z hz
      have hc := counts U f finj (fun x => F.Adj x z) (fun x => W.Adj x z)
        (fun x hx => adj x hx z hz)
      rw [imageU] at hc
      simpa only [cardU, ← hc] using hh z hz
  refine ⟨F, hF, adjF, ?_⟩
  intro sigma hsigma
  dsimp only
  intro hI
  let B : SimpleGraph (S ⊕ T) := SimpleGraph.fromRel fun v z =>
    ∃ u : U, ∃ w : Z, v = tau u ∧ z = w ∧ F.Adj u w ∧ J.Adj (sigma u) w
  letI : DecidableRel B.Adj := Classical.decRel _
  have adjB : ∀ u : U, ∀ z : Z,
      B.Adj (tau u) z ↔ F.Adj u z ∧ J.Adj (sigma u) z := by
    intro u z
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · obtain ⟨v, w, hv, hw, ha⟩ := hh
        have huv : u = v := tau.injective (Subtype.ext hv)
        have hzw : z = w := Subtype.ext hw
        simpa only [huv, hzw] using ha
      · obtain ⟨v, w, hv, hw, _⟩ := hh
        exact False.elim (Finset.disjoint_left.mp hVZ
          (Finset.mem_of_mem_erase (tau v).property) (hv ▸ z.property))
    · intro ha
      refine ⟨?_, Or.inl ⟨u, z, rfl, rfl, ha⟩⟩
      intro he
      exact Finset.disjoint_left.mp hVZ
        (Finset.mem_of_mem_erase (tau u).property) (he ▸ z.property)
  let C := SimpleGraph.fromRel fun x y => x ∈ U ∧ y ∈ K
  have hC : PerfectMatching C U K hUK sigma := by
    refine ⟨hsigma, ?_⟩
    intro u
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨u.property, (sigma u).property⟩⟩
    intro he
    exact Finset.disjoint_left.mp hUK u.property (he ▸ (sigma u).property)
  have partV : ∀ v : S ⊕ T, v ∈ V.erase v0 ↔ ∃ u : U, v = tau u := by
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
  have residualM : ∀ u : U, ∀ v : V.erase v0, M.Adj u v ↔ v = tau u := by
    intro u v
    simpa only [Subtype.ext_iff] using
      hM u ⟨v, Finset.mem_of_mem_erase v.property⟩
  letI : DecidableRel M.Adj := Classical.decRel _
  have hB := MatchingInducedUpdatedCandidacyTransport U (V.erase v0) K Z tau sigma
    M C F J B (V.erase v0) Z omega (p * h) hUK hC residualM adjB partV partZ hI
  let Anew := SimpleGraph.fromRel fun v z =>
    v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
      ∀ u : U, M.Adj u v → H.Adj (sigma u) z
  letI : DecidableRel Anew.Adj := Classical.decRel _
  have hBA : B ≤ Anew := by
    intro v z hvz
    rw [SimpleGraph.fromRel_adj] at hvz ⊢
    refine ⟨hvz.1, ?_⟩
    have forward : ∀ (v z : S ⊕ T),
        (∃ u : U, ∃ w : Z, v = tau u ∧ z = w ∧ F.Adj u w ∧ J.Adj (sigma u) w) →
        v ∈ V ∧ z ∈ Z ∧ O.Adj v z ∧
          ∀ u : U, M.Adj u v → H.Adj (sigma u) z := by
      rintro v z ⟨u, w, rfl, rfl, hfu, hju⟩
      refine ⟨Finset.mem_of_mem_erase (tau u).property, w.property,
        hWO ((adjF u w).mp hfu), ?_⟩
      intro u' hm
      have he : u = u' := tau.injective (Subtype.ext
        ((hM u' ⟨tau u, Finset.mem_of_mem_erase (tau u).property⟩).mp hm))
      simpa only [he] using hJH hju
    exact hvz.2.elim (fun hh => Or.inl (forward v z hh))
      (fun hh => Or.inr (forward z v hh))
  have hxZ : v0 ∉ Z := fun hz => Finset.disjoint_left.mp hVZ hv0 hz
  have row : ∀ z ∈ Z, Anew.Adj v0 z ↔ O.Adj v0 z := by
    intro z hz
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, hh | hh⟩
      · exact hh.2.2.1
      · exact (hxZ hh.2.1).elim
    · intro ha
      refine ⟨?_, Or.inl ⟨hv0, hz, ha, ?_⟩⟩
      · intro he
        exact hxZ (he ▸ hz)
      · intro u hm
        have he := (hM u ⟨v0, hv0⟩).mp hm
        exact ((Finset.mem_erase.mp (tau u).property).1 he.symm).elim
  have rowCount : (Z.filter fun z => Anew.Adj v0 z).card =
      (Z.filter fun z => O.Adj v0 z).card := by
    congr 1
    exact Finset.filter_congr row
  have hn0 : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hnt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hz0 : (Z.card : ENNReal) ≠ 0 := by simp [hZ]
  have hzt : (Z.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have heOldFinite : eOld ≠ ⊤ := ne_of_lt (heOld.trans_lt ENNReal.one_lt_top)
  have oldLower := (hO.2.1 v0 hv0).1
  have hpOldFinite : pOld ≠ ⊤ := by
    intro ht
    have hh : (⊤ : ENNReal) ≤ ((Z.filter fun z => O.Adj v0 z).card : ENNReal) := by
      simpa only [ht, ENNReal.top_sub heOldFinite, ENNReal.top_mul hz0] using oldLower
    exact (ENNReal.natCast_ne_top _) (top_le_iff.mp hh)
  have oldGap : p * h + 1 / (n : ENNReal) ≤ pOld - eOld := by
    apply ENNReal.le_sub_of_add_le_right heOldFinite
    calc
      (p * h + 1 / (n : ENNReal)) + eOld = p * h + eOld + 1 / (n : ENNReal) := by
        ac_rfl
      _ ≤ pOld := hgap
  have hphFinite : p * h ≠ ⊤ := ne_of_lt (hph.trans_lt ENNReal.one_lt_top)
  have hdFinite : p * h * (Z.card : ENNReal) ≠ ⊤ := ENNReal.mul_ne_top hphFinite hzt
  let k : ℕ := ⌊(p * h * (Z.card : ENNReal)).toReal⌋₊
  have hk : (k : ENNReal) ≤ p * h * (Z.card : ENNReal) := by
    have hh := ENNReal.ofReal_le_ofReal
      (Nat.floor_le (ENNReal.toReal_nonneg : 0 ≤ (p * h * (Z.card : ENNReal)).toReal))
    simpa only [k, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hdFinite] using hh
  have hkRound : p * h * (Z.card : ENNReal) ≤ (k : ENNReal) + 1 := by
    have hh := ENNReal.ofReal_le_ofReal
      (Nat.lt_floor_add_one (p * h * (Z.card : ENNReal)).toReal).le
    simpa only [k, ENNReal.ofReal_toReal hdFinite,
      ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh
  have hInv : 1 / (n : ENNReal) ≤ eps :=
    (ENNReal.div_le_div_right (by norm_num : (1 : ENNReal) ≤ 2) _).trans
      ((le_add_left le_rfl).trans houter)
  have hreserve : (1 : ENNReal) ≤ eps * (Z.card : ENNReal) := by
    calc
      1 = (1 / (n : ENNReal)) * n := (ENNReal.div_mul_cancel hn0 hnt).symm
      _ ≤ eps * n := mul_le_mul_left hInv _
      _ ≤ eps * (Z.card : ENNReal) := mul_le_mul_right
        (by exact_mod_cast (by omega : n ≤ Z.card)) eps
  have hkLower : (p * h - eps) * (Z.card : ENNReal) ≤ k := by
    rw [ENNReal.sub_mul (fun _ _ => hzt), tsub_le_iff_right]
    exact hkRound.trans (add_le_add le_rfl hreserve)
  have hkUpper : (k : ENNReal) ≤ (p * h + eps) * (Z.card : ENNReal) :=
    hk.trans (mul_le_mul_left (le_add_right le_rfl) _)
  have hkAvailable : k ≤ (Z.filter fun z => Anew.Adj v0 z).card := by
    rw [rowCount]
    exact_mod_cast hk.trans ((mul_le_mul_left
      ((le_add_right le_rfl).trans oldGap) _).trans oldLower)
  obtain ⟨N, Wnew, _, _, _, hsub, _, _, hnew⟩ :=
    FutureExtraVertexStability n k omega eps (p * h) hn homega heps hph
      houter houterReg B Anew (V.erase v0) Z v0
      (hVZ.mono_left (Finset.erase_subset _ _)) (Finset.notMem_erase _ _)
      hxZ (by rw [cardU, hU]) (Or.inr hZ) hBA hkAvailable hkLower hkUpper hB
  refine ⟨Wnew, hsub, ?_⟩
  simpa only [Finset.insert_erase hv0] using hnew
