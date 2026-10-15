import Tablet.Preamble

-- [TABLET NODE: BipartiteSelectedEdgeGraph]
theorem BipartiteSelectedEdgeGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U W : Finset V) (hUW : Disjoint U W)
    (P : U → W → Prop) [DecidableRel P] (k : ℕ)
    (hG : ∀ (u : U) (w : W), P u w → G.Adj u.val w.val)
    (hrow : ∀ u : U, (Finset.univ.filter fun w : W => P u w).card = k)
    (hcol : ∀ w : W, (Finset.univ.filter fun u : U => P u w).card = k) :
    ∃ F : SimpleGraph V, F ≤ G ∧
      (∀ u ∈ U, {w | w ∈ W ∧ F.Adj u w}.ncard = k) ∧
      (∀ w ∈ W, {u | u ∈ U ∧ F.Adj u w}.ncard = k) ∧
      (∀ (u : U) (w : W), F.Adj u.val w.val ↔ P u w) := by
-- BODY
  classical
  let F : SimpleGraph V :=
    { Adj := fun a b =>
        (∃ (ha : a ∈ U) (hb : b ∈ W), P ⟨a, ha⟩ ⟨b, hb⟩) ∨
        (∃ (hb : b ∈ U) (ha : a ∈ W), P ⟨b, hb⟩ ⟨a, ha⟩)
      symm := fun _ _ h => h.symm
      loopless := by
        constructor
        intro a h
        rcases h with ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩
        · exact Finset.disjoint_left.mp hUW ha hb
        · exact Finset.disjoint_left.mp hUW ha hb }
  have hadj (u : U) (w : W) : F.Adj u.val w.val ↔ P u w := by
    constructor
    · rintro (⟨hu, hw, hp⟩ | ⟨hw, hu, hp⟩)
      · exact hp
      · exact (Finset.disjoint_left.mp hUW u.property hu).elim
    · intro hp
      exact Or.inl ⟨u.property, w.property, hp⟩
  refine ⟨F, ?_, ?_, ?_, hadj⟩
  · intro a b h
    rcases h with ⟨ha, hb, hp⟩ | ⟨hb, ha, hp⟩
    · exact hG ⟨a, ha⟩ ⟨b, hb⟩ hp
    · exact (hG ⟨b, hb⟩ ⟨a, ha⟩ hp).symm
  · intro u hu
    have he : {w | w ∈ W ∧ F.Adj u w} =
        Subtype.val '' (↑(Finset.univ.filter fun w : W => P ⟨u, hu⟩ w) : Set W) := by
      ext w
      constructor
      · rintro ⟨hw, hf⟩
        exact ⟨⟨w, hw⟩, by simpa using (hadj ⟨u, hu⟩ ⟨w, hw⟩).mp hf, rfl⟩
      · rintro ⟨w', hp, rfl⟩
        exact ⟨w'.property, (hadj ⟨u, hu⟩ w').mpr (by simpa using hp)⟩
    rw [he, Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_coe_finset, hrow]
  · intro w hw
    have he : {u | u ∈ U ∧ F.Adj u w} =
        Subtype.val '' (↑(Finset.univ.filter fun u : U => P u ⟨w, hw⟩) : Set U) := by
      ext u
      constructor
      · rintro ⟨hu, hf⟩
        exact ⟨⟨u, hu⟩, by simpa using (hadj ⟨u, hu⟩ ⟨w, hw⟩).mp hf, rfl⟩
      · rintro ⟨u', hp, rfl⟩
        exact ⟨u'.property, (hadj u' ⟨w, hw⟩).mpr (by simpa using hp)⟩
    rw [he, Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_coe_finset, hcol]
