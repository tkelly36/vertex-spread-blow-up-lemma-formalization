import Tablet.MatchingInducedGraph
import Tablet.UpdatedCandidacyCluster
import Tablet.SuperRegularPair
import Tablet.PerfectMatching

-- [TABLET NODE: MatchingInducedUpdatedCandidacyTransport]
theorem MatchingInducedUpdatedCandidacyTransport :
    ∀ {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
      (L₁ L₂ K R : Finset (S ⊕ T))
      (τ : L₁ ≃ L₂) (σ : L₁ → K)
      (M F₁₂ F₁₃ F₂₃ : SimpleGraph (S ⊕ T))
      [DecidableRel M.Adj] [DecidableRel F₁₂.Adj]
      [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
      (A' : SimpleGraph (S ⊕ T)) [DecidableRel A'.Adj]
      (L' R' : Finset (S ⊕ T)) (ε d : ENNReal),
      (h₁₂ : Disjoint L₁ K) →
      PerfectMatching F₁₂ L₁ K h₁₂ σ →
      (∀ x : L₁, ∀ y : L₂, M.Adj x y ↔ y = τ x) →
      (∀ x : L₁, ∀ z : R,
        A'.Adj (τ x) z ↔ F₁₃.Adj x z ∧ F₂₃.Adj (σ x) z) →
      (∀ y : S ⊕ T, y ∈ L' ↔ ∃ x : L₁, y = τ x) →
      (∀ z : S ⊕ T, z ∈ R' ↔ ∃ w : R, z = w) →
      let J := MatchingInducedGraph F₁₃ F₂₃ L₁ K R σ
      let JL : Finset (L₁ ⊕ R) := Finset.univ.image Sum.inl
      let JR : Finset (L₁ ⊕ R) := Finset.univ.image Sum.inr
      (letI : DecidableRel J.Adj := Classical.decRel _
       SuperRegularPair J JL JR ε d) →
      SuperRegularPair A' L' R' ε d := by
-- BODY
  intro S T _ _ _ _ L₁ L₂ K R τ σ M F₁₂ F₁₃ F₂₃ _ _ _ _ A' _
    L' R' ε d h₁₂ hσ hM hA hL hR
  classical
  dsimp only
  let J := MatchingInducedGraph F₁₃ F₂₃ L₁ K R σ
  letI : DecidableRel J.Adj := Classical.decRel _
  let JL : Finset (L₁ ⊕ R) := Finset.univ.image Sum.inl
  let JR : Finset (L₁ ⊕ R) := Finset.univ.image Sum.inr
  intro hJ
  change SuperRegularPair J JL JR ε d at hJ
  let f : L₁ ⊕ R → S ⊕ T := Sum.elim (fun x => (τ x).val) Subtype.val
  have left : ∀ p ∈ JL, ∃ x : L₁, p = Sum.inl x := by
    intro p hp
    simpa [JL, eq_comm] using hp
  have right : ∀ q ∈ JR, ∃ z : R, q = Sum.inr z := by
    intro q hq
    simpa [JR, eq_comm] using hq
  have injL : Set.InjOn f JL := by
    intro p hp q hq he
    obtain ⟨x, rfl⟩ := left p hp
    obtain ⟨y, rfl⟩ := left q hq
    exact congrArg Sum.inl (τ.injective (Subtype.ext he))
  have injR : Set.InjOn f JR := by
    intro p hp q hq he
    obtain ⟨x, rfl⟩ := right p hp
    obtain ⟨y, rfl⟩ := right q hq
    exact congrArg Sum.inr (Subtype.ext he)
  have imageL : JL.image f = L' := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, rfl⟩ := left p hp
      exact (hL _).2 ⟨x, rfl⟩
    · intro hy
      obtain ⟨x, rfl⟩ := (hL y).1 hy
      exact ⟨Sum.inl x, by simp [JL], rfl⟩
  have imageR : JR.image f = R' := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨w, rfl⟩ := right q hq
      exact (hR _).2 ⟨w, rfl⟩
    · intro hz
      obtain ⟨w, rfl⟩ := (hR z).1 hz
      exact ⟨Sum.inr w, by simp [JR], rfl⟩
  have adj : ∀ p ∈ JL, ∀ q ∈ JR, J.Adj p q ↔ A'.Adj (f p) (f q) := by
    intro p hp q hq
    obtain ⟨x, rfl⟩ := left p hp
    obtain ⟨z, rfl⟩ := right q hq
    change J.Adj (Sum.inl x) (Sum.inr z) ↔ A'.Adj (τ x) z
    rw [hA x z]
    simp only [J, MatchingInducedGraph, SimpleGraph.fromRel_adj,
      Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inl.injEq, Sum.inr.injEq,
      false_and, exists_false, or_false]
    constructor
    · rintro ⟨_, a, b, rfl, rfl, hab⟩
      exact hab
    · intro hab
      refine ⟨?_, x, z, rfl, rfl, hab⟩
      intro he
      cases he
  have cardL : L'.card = JL.card := by
    rw [← imageL]
    exact Finset.card_image_iff.mpr injL
  have cardR : R'.card = JR.card := by
    rw [← imageR]
    exact Finset.card_image_iff.mpr injR
  have pull : ∀ (P U : Finset (L₁ ⊕ R)) (V : Finset (S ⊕ T)),
      U = P.filter (fun p => f p ∈ V) → V ⊆ P.image f → U.image f = V := by
    intro P U V hU hV
    subst U
    ext v
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp, hv⟩, rfl⟩
      exact hv
    · intro hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (hV hv)
      exact ⟨p, ⟨hp, hv⟩, rfl⟩
  have edges : ∀ U ⊆ JL, ∀ W ⊆ JR,
      ((U.product W).filter fun p => J.Adj p.1 p.2).card =
        (((U.image f).product (W.image f)).filter
          fun p => A'.Adj p.1 p.2).card := by
    intro U hU W hW
    apply Finset.card_bij (fun p _ => (f p.1, f p.2))
    · intro p hp
      obtain ⟨hp, ha⟩ := Finset.mem_filter.mp hp
      obtain ⟨hu, hw⟩ := Finset.mem_product.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨p.1, hu, rfl⟩,
         Finset.mem_image.mpr ⟨p.2, hw, rfl⟩⟩,
        (adj _ (hU hu) _ (hW hw)).mp ha⟩
    · intro p hp q hq he
      have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have hq' := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      exact Prod.ext (injL (hU hp'.1) (hU hq'.1) (congrArg Prod.fst he))
        (injR (hW hp'.2) (hW hq'.2) (congrArg Prod.snd he))
    · intro p hp
      obtain ⟨hp, ha⟩ := Finset.mem_filter.mp hp
      obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hl
      obtain ⟨w, hw, hf⟩ := Finset.mem_image.mp hr
      refine ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hw⟩, ?_⟩,
        Prod.ext he hf⟩
      exact (adj _ (hU hu) _ (hW hw)).mpr (by simpa [he, hf] using ha)
  have neighborhoods : ∀ (P : Finset (L₁ ⊕ R)) (hinj : Set.InjOn f P)
      (a : L₁ ⊕ R → Prop) (b : S ⊕ T → Prop)
      [DecidablePred a] [DecidablePred b],
      (∀ p ∈ P, a p ↔ b (f p)) →
      (P.filter a).card = ((P.image f).filter b).card := by
    intro P hinj a b _ _ hab
    apply Finset.card_bij (fun p _ => f p)
    · intro p hp
      obtain ⟨hp, ha⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, (hab p hp).mp ha⟩
    · intro p hp q hq he
      exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
    · intro v hv
      obtain ⟨hv, hb⟩ := Finset.mem_filter.mp hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, (hab p hp).mpr hb⟩, rfl⟩
  rcases hJ with ⟨hreg, hdegL, hdegR⟩
  refine ⟨?_, ?_, ?_⟩
  · intro V hV Z hZ hv hz
    let U := JL.filter (fun p => f p ∈ V)
    let W := JR.filter (fun q => f q ∈ Z)
    have hU : U ⊆ JL := Finset.filter_subset _ _
    have hW : W ⊆ JR := Finset.filter_subset _ _
    have hUV : U.image f = V := pull JL U V rfl (by simpa [imageL] using hV)
    have hWZ : W.image f = Z := pull JR W Z rfl (by simpa [imageR] using hZ)
    have cu : V.card = U.card := by
      rw [← hUV]
      exact Finset.card_image_iff.mpr (injL.mono hU)
    have cw : Z.card = W.card := by
      rw [← hWZ]
      exact Finset.card_image_iff.mpr (injR.mono hW)
    have density : PairDensity J U W = PairDensity A' V Z := by
      unfold PairDensity
      rw [← hUV, ← hWZ, edges U hU W hW,
        Finset.card_image_iff.mpr (injL.mono hU),
        Finset.card_image_iff.mpr (injR.mono hW)]
    rw [cardL, cu] at hv
    rw [cardR, cw] at hz
    simpa only [density] using hreg U hU W hW hv hz
  · intro y hy
    rw [← imageL] at hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have hc := neighborhoods JR injR (fun q => J.Adj p q)
      (fun z => A'.Adj (f p) z) (fun q hq => adj p hp q hq)
    rw [imageR] at hc
    simpa only [cardR, ← hc] using hdegL p hp
  · intro z hz
    rw [← imageR] at hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    have hc := neighborhoods JL injL (fun p => J.Adj p q)
      (fun y => A'.Adj y (f q)) (fun p hp => adj p hp q hq)
    rw [imageL] at hc
    simpa only [cardL, ← hc] using hdegR q hq
