import Tablet.ReducedSquareColoring

-- [TABLET NODE: ColourRoundUntouchedGeometry]
theorem ColourRoundUntouchedGeometry
    {r q : ℕ} (R : SimpleGraph (Fin r)) [DecidableRel R.Adj]
    (colour : Fin r → Fin q) (D round : ℕ) (touched : Finset (Fin r))
    (i : Fin r)
    (hdegree : ∀ j, (Finset.univ.filter fun k => R.Adj j k).card ≤ D)
    (hcolour : ∀ ⦃u v⦄, u ≠ v →
      (R.Adj u v ∨ ∃ k, R.Adj u k ∧ R.Adj k v) → colour u ≠ colour v)
    (htouched : ∀ j ∈ touched, (colour j).val = round)
    (hi : (colour i).val = round) (hiS : i ∉ touched) :
    (touched.filter fun k => R.Adj i k) = ∅ ∧
    (∀ j, R.Adj i j → (touched.filter fun k => R.Adj j k) = ∅) ∧
    (∀ j, ((insert i touched).filter fun k => R.Adj j k).card ≤ 1) ∧
    (∀ j, R.Adj i j →
      (Finset.univ.filter fun k =>
        ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card < D ∧
      (Finset.univ.filter fun k =>
        ((colour k).val < round ∨ k ∈ insert i touched) ∧ R.Adj j k).card =
        (Finset.univ.filter fun k =>
          ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card + 1) := by
-- BODY
  classical
  have same (s : Fin r) (hs : s ∈ touched) : colour i = colour s :=
    Fin.ext (hi.trans (htouched s hs).symm)
  have untouchedCurrent : (touched.filter fun k => R.Adj i k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hadj
    exact hcolour (R.ne_of_adj hadj) (Or.inl hadj) (same s hs)
  have untouchedFuture (j : Fin r) (hij : R.Adj i j) :
      (touched.filter fun k => R.Adj j k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hjs
    have his : i ≠ s := fun h => hiS (h.symm ▸ hs)
    exact hcolour his (Or.inr ⟨j, hij, hjs⟩) (same s hs)
  refine ⟨untouchedCurrent, untouchedFuture, ?_, ?_⟩
  · intro j
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huS, hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvS, hjv⟩ := Finset.mem_filter.mp hv
    have hval (s : Fin r) (hs : s ∈ insert i touched) :
        (colour s).val = round := by
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hi
      · exact htouched s hs
    by_contra huv
    exact hcolour huv (Or.inr ⟨j, R.symm hju, hjv⟩)
      (Fin.ext ((hval u huS).trans (hval v hvS).symm))
  · intro j hij
    let E := Finset.univ.filter fun k =>
      ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k
    have hiE : i ∉ E := by
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, hi,
        lt_self_iff_false, false_or, hiS, false_and, not_false_eq_true]
    have eqE : (Finset.univ.filter fun k =>
        ((colour k).val < round ∨ k ∈ insert i touched) ∧ R.Adj j k) =
        insert i E := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, E]
      constructor
      · rintro ⟨hk | (rfl | hk), hjk⟩
        · exact Or.inr ⟨Or.inl hk, hjk⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inr hk, hjk⟩
      · rintro (rfl | ⟨hk, hjk⟩)
        · exact ⟨Or.inr (Or.inl rfl), R.symm hij⟩
        · exact ⟨hk.imp id Or.inr |> Or.imp id id, hjk⟩
    have hsub : insert i E ⊆ Finset.univ.filter fun k => R.Adj j k := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, R.symm hij⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.2⟩
    have hbound := (Finset.card_le_card hsub).trans (hdegree j)
    rw [Finset.card_insert_of_notMem hiE] at hbound
    exact ⟨by change E.card < D; omega,
      by rw [eqE, Finset.card_insert_of_notMem hiE]⟩
