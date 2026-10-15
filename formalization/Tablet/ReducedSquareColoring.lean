import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: ReducedSquareColoring]
theorem ReducedSquareColoring :
    ∀ {r D : ℕ} (R : SimpleGraph (Fin r)) [DecidableRel R.Adj],
      R.maxDegree ≤ D →
      ∃ q : ℕ, 0 < q ∧ q ≤ D ^ 2 + 1 ∧
        ∃ colour : Fin r → Fin q,
          ∀ ⦃i j : Fin r⦄, i ≠ j →
            (R.Adj i j ∨ ∃ k : Fin r, R.Adj i k ∧ R.Adj k j) →
            colour i ≠ colour j := by
-- BODY
  classical
  intro r D R _ hD
  let S : SimpleGraph (Fin r) :=
    { Adj := fun i j => i ≠ j ∧
        (R.Adj i j ∨ ∃ k, R.Adj i k ∧ R.Adj k j)
      symm := by
        intro i j h
        refine ⟨h.1.symm, ?_⟩
        rcases h.2 with h | ⟨k, hik, hkj⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨k, hkj.symm, hik.symm⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  have hdegree (v : Fin r) : R.degree v ≤ D :=
    (R.degree_le_maxDegree v).trans hD
  have hsdegree (v : Fin r) : S.degree v ≤ D ^ 2 := by
    let block : Fin r → Finset (Fin r) :=
      fun u => insert u ((R.neighborFinset u).erase v)
    have hblock (u : Fin r) (hu : u ∈ R.neighborFinset v) :
        (block u).card = R.degree u := by
      have hv : v ∈ R.neighborFinset u := by
        exact (R.mem_neighborFinset _ _).2 ((R.mem_neighborFinset _ _).1 hu).symm
      have hnot : u ∉ (R.neighborFinset u).erase v := by
        simp
      change (insert u ((R.neighborFinset u).erase v)).card = R.degree u
      rw [Finset.card_insert_of_notMem hnot]
      exact Finset.card_erase_add_one hv
    have hsub : S.neighborFinset v ⊆ (R.neighborFinset v).biUnion block := by
      intro w hw
      have hw' : v ≠ w ∧ (R.Adj v w ∨ ∃ k, R.Adj v k ∧ R.Adj k w) :=
        (S.mem_neighborFinset _ _).1 hw
      apply Finset.mem_biUnion.mpr
      rcases hw'.2 with hvw | ⟨u, hvu, huw⟩
      · exact ⟨w, (R.mem_neighborFinset _ _).2 hvw, Finset.mem_insert_self _ _⟩
      · refine ⟨u, (R.mem_neighborFinset _ _).2 hvu, Finset.mem_insert_of_mem ?_⟩
        exact Finset.mem_erase.mpr ⟨hw'.1.symm, (R.mem_neighborFinset _ _).2 huw⟩
    calc
      S.degree v = (S.neighborFinset v).card := rfl
      _ ≤ ((R.neighborFinset v).biUnion block).card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ R.neighborFinset v, (block u).card := Finset.card_biUnion_le
      _ = ∑ u ∈ R.neighborFinset v, R.degree u := Finset.sum_congr rfl hblock
      _ ≤ ∑ _u ∈ R.neighborFinset v, D := Finset.sum_le_sum fun u _ => hdegree u
      _ = R.degree v * D := by
        rw [Finset.sum_const, smul_eq_mul]
        rfl
      _ ≤ D * D := Nat.mul_le_mul_right D (hdegree v)
      _ = D ^ 2 := (pow_two D).symm
  let q := D ^ 2 + 1
  have hq : 0 < q := Nat.zero_lt_succ _
  -- Extend a colouring of a finite set by choosing outside its forbidden image.
  have hcolour (s : Finset (Fin r)) :
      ∃ c : Fin r → Fin q,
        ∀ i ∈ s, ∀ j ∈ s, S.Adj i j → c i ≠ c j := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => ⟨0, hq⟩, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨c, hc⟩ := ih
        let forbidden := ((S.neighborFinset a) ∩ s).image c
        have hcard : forbidden.card < (Finset.univ : Finset (Fin q)).card := by
          calc
            forbidden.card ≤ ((S.neighborFinset a) ∩ s).card := Finset.card_image_le
            _ ≤ (S.neighborFinset a).card := Finset.card_le_card Finset.inter_subset_left
            _ ≤ D ^ 2 := hsdegree a
            _ < (Finset.univ : Finset (Fin q)).card := by simp [q]
        obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hbne (j : Fin r) (hj : j ∈ s) (hadj : S.Adj a j) : b ≠ c j := by
          intro heq
          apply hb
          exact Finset.mem_image.mpr
            ⟨j, Finset.mem_inter.mpr ⟨(S.mem_neighborFinset _ _).2 hadj, hj⟩,
              heq.symm⟩
        refine ⟨fun i => if i = a then b else c i, ?_⟩
        intro i hi j hj hij
        by_cases hia : i = a
        · subst i
          have hja : j ≠ a := hij.ne.symm
          have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
          simpa only [if_pos rfl, if_neg hja] using hbne j hjs hij
        · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            simpa only [if_pos rfl, if_neg hia] using (hbne i his hij.symm).symm
          · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
            simpa only [if_neg hia, if_neg hja] using hc i his j hjs hij
  obtain ⟨c, hc⟩ := hcolour Finset.univ
  refine ⟨q, hq, le_rfl, c, ?_⟩
  intro i j hne hadj
  exact hc i (Finset.mem_univ _) j (Finset.mem_univ _) ⟨hne, hadj⟩
