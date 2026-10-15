import Tablet.SuperRegularPair

-- [TABLET NODE: SuperRegularPairEmbedding]
theorem SuperRegularPairEmbedding
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V → W) (hinj : Function.Injective e)
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (L R : Finset V) (eps d : ENNReal)
    (hadj : ∀ x ∈ L, ∀ y ∈ R, H.Adj (e x) (e y) ↔ G.Adj x y)
    (hG : SuperRegularPair G L R eps d) :
    SuperRegularPair H (L.image e) (R.image e) eps d := by
-- BODY
  classical
  have card (S : Finset V) : (S.image e).card = S.card :=
    Finset.card_image_of_injective S hinj
  have density (P Q : Finset V) (hP : P ⊆ L) (hQ : Q ⊆ R) :
      PairDensity H (P.image e) (Q.image e) = PairDensity G P Q := by
    have edges :
        (((P.image e).product (Q.image e)).filter fun p => H.Adj p.1 p.2) =
        ((P.product Q).filter fun p => G.Adj p.1 p.2).image (Prod.map e e) := by
      change (((P.image e) ×ˢ (Q.image e)).filter _) = _
      rw [← Finset.prodMap_image_product, Finset.filter_image]
      congr 1
      apply Finset.filter_congr
      intro p hp
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hp
      exact hadj p.1 (hP hp) p.2 (hQ hq)
    unfold PairDensity
    rw [edges, Finset.card_image_of_injective _ (hinj.prodMap hinj), card, card]
  have left (x : V) (hx : x ∈ L) :
      ((R.image e).filter fun y => H.Adj (e x) y).card =
        (R.filter fun y => G.Adj x y).card := by
    rw [Finset.filter_image]
    have hh : R.filter (fun y => H.Adj (e x) (e y)) =
        R.filter (fun y => G.Adj x y) :=
      Finset.filter_congr fun y hy => hadj x hx y hy
    rw [hh, card]
  have right (y : V) (hy : y ∈ R) :
      ((L.image e).filter fun x => H.Adj x (e y)).card =
        (L.filter fun x => G.Adj x y).card := by
    rw [Finset.filter_image]
    have hh : L.filter (fun x => H.Adj (e x) (e y)) =
        L.filter (fun x => G.Adj x y) :=
      Finset.filter_congr fun x hx => hadj x hx y hy
    rw [hh, card]
  refine ⟨?_, ?_, ?_⟩
  · intro P hP Q hQ hsizeP hsizeQ
    let P0 := L.filter fun x => e x ∈ P
    let Q0 := R.filter fun x => e x ∈ Q
    have pull (S : Finset V) (A : Finset W) (hA : A ⊆ S.image e) :
        (S.filter fun x => e x ∈ A).image e = A := by
      ext y
      constructor
      · rintro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hA hy)
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hy⟩, rfl⟩
    have hp : P0.image e = P := pull L P hP
    have hq : Q0.image e = Q := pull R Q hQ
    rw [← hp, card, card] at hsizeP
    rw [← hq, card, card] at hsizeQ
    rw [← hp, ← hq, density P0 Q0 (Finset.filter_subset _ _) (Finset.filter_subset _ _)]
    exact hG.1 P0 (Finset.filter_subset _ _) Q0 (Finset.filter_subset _ _)
      hsizeP hsizeQ
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simpa only [card, left a ha] using hG.2.1 a ha
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    simpa only [card, right b hb] using hG.2.2 b hb
