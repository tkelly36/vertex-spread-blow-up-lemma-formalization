import Tablet.MatchingInducedGraph

-- [TABLET NODE: MatchingInducedGraphIdentities]
theorem MatchingInducedGraphIdentities
    {V : Type*} [Fintype V] [DecidableEq V]
    (F H : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel H.Adj]
    (U W Z : Finset V) (f : U → W) :
    let A := MatchingInducedGraph F H U W Z f
    letI : DecidableRel A.Adj := Classical.decRel _
    let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
    let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
    L.card = U.card ∧ R.card = Z.card ∧ Disjoint L R ∧
    (∀ (x : U) (z : Z), A.Adj (Sum.inl x) (Sum.inr z) ↔
      F.Adj x z ∧ H.Adj (f x) z) ∧
    (∀ x : U, (R.filter fun z => A.Adj (Sum.inl x) z).card =
      (Z.filter fun z => F.Adj x z ∧ H.Adj (f x) z).card) ∧
    (∀ z : Z, (L.filter fun x => A.Adj x (Sum.inr z)).card =
      (Finset.univ.filter fun x : U => F.Adj x z ∧ H.Adj (f x) z).card) ∧
    (∀ z z' : Z,
      (L.filter fun x => A.Adj x (Sum.inr z) ∧ A.Adj x (Sum.inr z')).card =
      (Finset.univ.filter fun x : U =>
        (F.Adj x z ∧ F.Adj x z') ∧ (H.Adj (f x) z ∧ H.Adj (f x) z')).card) := by
-- BODY
  classical
  dsimp only
  have hcross (x : U) (z : Z) :
      (MatchingInducedGraph F H U W Z f).Adj (Sum.inl x) (Sum.inr z) ↔
        F.Adj x z ∧ H.Adj (f x) z := by
    change (_ ∧ ((∃ a : U, ∃ b : Z, _ ∧ _ ∧ _) ∨ _)) ↔ _
    constructor
    · rintro ⟨_, ⟨a, b, ha, hb, h⟩ | ⟨a, b, ha, _⟩⟩
      · cases Sum.inl.inj ha
        cases Sum.inr.inj hb
        exact h
      · cases ha
    · intro h
      exact ⟨Sum.inl_ne_inr, Or.inl ⟨x, z, rfl, rfl, h⟩⟩
  refine ⟨?_, ?_, ?_, hcross, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Sum.inl_injective]
    simp
  · rw [Finset.card_image_of_injective _ Sum.inr_injective]
    simp
  · apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hy'
    cases hz
  · intro x
    rw [Finset.filter_image, Finset.card_image_of_injective _ Sum.inr_injective]
    apply Finset.card_bij (fun z _ => z.1)
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcross] at hz
      exact Finset.mem_filter.mpr ⟨z.property, hz⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro z hz
      refine ⟨⟨z, (Finset.mem_filter.mp hz).1⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hcross]
        using (Finset.mem_filter.mp hz).2
  · intro z
    rw [Finset.filter_image, Finset.card_image_of_injective _ Sum.inl_injective]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcross]
  · intro z z'
    rw [Finset.filter_image, Finset.card_image_of_injective _ Sum.inl_injective]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcross]
    tauto
