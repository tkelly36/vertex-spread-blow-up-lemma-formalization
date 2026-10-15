import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

-- [TABLET NODE: RegularExtractionIneligibleArea]
theorem RegularExtractionIneligibleArea
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (n l : ℕ) (γ α : ℝ)
    (hU : U.card = n) (hW : W.card = n)
    (hl : 1 ≤ l) (hγ : 0 < γ) (hα : 0 < α)
    (P : Finpartition (Finset.univ : Finset V))
    (heq : P.IsEquipartition) (hlP : l ≤ P.parts.card)
    (hPn : P.parts.card ≤ n)
    (htotal : (Finset.univ : Finset V).card = 2 * n)
    (hunif : P.IsUniform G α)
    (hsize : ∀ S ∈ P.parts, (S.card : ℝ) ≤ 3 * n / P.parts.card)
    (E : Finset (Finset V × Finset V))
    (hE : ∀ S T, (S, T) ∈ E ↔
      S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T ∧ G.IsUniform α S T ∧
      γ * S.card ≤ ((U ∩ S).card : ℝ) ∧
      γ * T.card ≤ ((W ∩ T).card : ℝ)) :
    (∑ ST ∈ (P.parts.product P.parts).filter (fun ST => ST ∉ E),
      (((U ∩ ST.1).card : ℝ) * (W ∩ ST.2).card)) ≤
      (4 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2 := by
-- BODY
  classical
  let m := P.parts.card
  have hm : 0 < m := lt_of_lt_of_le (by omega : 0 < l) hlP
  have hn0 : 0 < n := hm.trans_le hPn
  have hmr : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hml : (l : ℝ) ≤ m := Nat.cast_le.mpr hlP
  have hmnr : (m : ℝ) ≤ n := Nat.cast_le.mpr hPn
  have hlr : 0 < (l : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsum : (∑ S ∈ P.parts, (S.card : ℝ)) = 2 * n := by
    exact_mod_cast P.sum_card_parts.trans htotal
  let a := fun S : Finset V => ((U ∩ S).card : ℝ)
  let b := fun S : Finset V => ((W ∩ S).card : ℝ)
  let c := fun S : Finset V => (S.card : ℝ)
  let R := P.parts.product P.parts
  have ha0 : ∀ S, 0 ≤ a S := fun S => Nat.cast_nonneg _
  have hb0 : ∀ S, 0 ≤ b S := fun S => Nat.cast_nonneg _
  have hc0 : ∀ S, 0 ≤ c S := fun S => Nat.cast_nonneg _
  have hac : ∀ S, a S ≤ c S := fun S =>
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
  have hbc : ∀ S, b S ≤ c S := fun S =>
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
  have hsum_inter : ∀ X : Finset V,
      (∑ S ∈ P.parts, ((X ∩ S).card : ℝ)) = X.card := by
    as_aux_lemma =>
    intro X
    have hpair : (P.parts : Set (Finset V)).PairwiseDisjoint (fun S => X ∩ S) := by
      intro S hS T hT hST
      exact (P.supIndep.pairwiseDisjoint hS hT hST).mono
        Finset.inter_subset_right Finset.inter_subset_right
    have hnat : (∑ S ∈ P.parts, (X ∩ S).card) = X.card := by
      rw [← Finset.card_biUnion hpair, ← Finset.inter_biUnion]
      change (X ∩ P.parts.biUnion id).card = X.card
      rw [P.biUnion_parts, Finset.inter_univ]
    exact_mod_cast hnat
  have ha : (∑ S ∈ P.parts, a S) = n := by
    simpa only [a, hU] using hsum_inter U
  have hb : (∑ S ∈ P.parts, b S) = n := by
    simpa only [b, hW] using hsum_inter W
  have hc : (∑ S ∈ P.parts, c S) = 2 * n := hsum
  have hbadU : (∑ S ∈ P.parts, if ¬γ * c S ≤ a S then a S else 0) ≤
      2 * γ * n := by
    calc
      _ ≤ ∑ S ∈ P.parts, γ * c S := by
        apply Finset.sum_le_sum
        intro S hS
        split_ifs with h
        · exact mul_nonneg hγ.le (hc0 S)
        · exact (lt_of_not_ge h).le
      _ = _ := by rw [← Finset.mul_sum, hc]; ring
  have hbadW : (∑ S ∈ P.parts, if ¬γ * c S ≤ b S then b S else 0) ≤
      2 * γ * n := by
    calc
      _ ≤ ∑ S ∈ P.parts, γ * c S := by
        apply Finset.sum_le_sum
        intro S hS
        split_ifs with h
        · exact mul_nonneg hγ.le (hc0 S)
        · exact (lt_of_not_ge h).le
      _ = _ := by rw [← Finset.mul_sum, hc]; ring
  have hareaU : (∑ ST ∈ R,
      if ¬γ * c ST.1 ≤ a ST.1 then a ST.1 * b ST.2 else 0) ≤
      2 * γ * (n : ℝ) ^ 2 := by
    as_aux_lemma =>
    calc
      _ = ∑ S ∈ P.parts,
          (if ¬γ * c S ≤ a S then a S else 0) * n := by
        change (∑ ST ∈ P.parts ×ˢ P.parts,
          if ¬γ * c ST.1 ≤ a ST.1 then a ST.1 * b ST.2 else 0) = _
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro S hS
        by_cases h : ¬γ * c S ≤ a S
        · simp only [h, not_false_eq_true, if_true, ← Finset.mul_sum, hb]
        · simp only [h, if_false, Finset.sum_const_zero, zero_mul]
      _ = (∑ S ∈ P.parts, if ¬γ * c S ≤ a S then a S else 0) * n :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * γ * n) * n := mul_le_mul_of_nonneg_right hbadU hnr.le
      _ = _ := by ring
  have hareaW : (∑ ST ∈ R,
      if ¬γ * c ST.2 ≤ b ST.2 then a ST.1 * b ST.2 else 0) ≤
      2 * γ * (n : ℝ) ^ 2 := by
    as_aux_lemma =>
    calc
      _ = ∑ S ∈ P.parts,
          a S * (∑ T ∈ P.parts, if ¬γ * c T ≤ b T then b T else 0) := by
        change (∑ ST ∈ P.parts ×ˢ P.parts,
          if ¬γ * c ST.2 ≤ b ST.2 then a ST.1 * b ST.2 else 0) = _
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        split_ifs <;> simp
      _ = n * (∑ T ∈ P.parts, if ¬γ * c T ≤ b T then b T else 0) := by
        rw [← Finset.sum_mul, ha]
      _ ≤ n * (2 * γ * n) := mul_le_mul_of_nonneg_left hbadW hnr.le
      _ = _ := by ring
  have hNUsub : P.nonUniforms G α ⊆ R := by
    rintro ⟨S, T⟩ hST
    rcases (P.mk_mem_nonUniforms G).mp hST with ⟨hS, hT, -, -⟩
    exact Finset.mem_product.mpr ⟨hS, hT⟩
  have hareaN : (∑ ST ∈ R,
      if ST ∈ P.nonUniforms G α then a ST.1 * b ST.2 else 0) ≤
      9 * α * (n : ℝ) ^ 2 := by
    as_aux_lemma =>
    have hV : (Finset.univ : Finset V).Nonempty := by
      apply Finset.card_pos.mp
      rw [htotal]
      omega
    have hu : (∑ ST ∈ P.nonUniforms G α, c ST.1 * c ST.2) <
        α * ((Finset.univ : Finset V).card + (P.parts.card : ℝ)) ^ 2 :=
      heq.sum_nonUniforms_lt' hV hα hunif
    have hscale : α * ((Finset.univ : Finset V).card + (P.parts.card : ℝ)) ^ 2 ≤
        9 * α * (n : ℝ) ^ 2 := by
      rw [htotal, Nat.cast_mul, Nat.cast_ofNat]
      have hsq : (2 * (n : ℝ) + m) ^ 2 ≤ (3 * n) ^ 2 := by
        nlinarith only [hmnr, hmr, hnr]
      have := mul_le_mul_of_nonneg_left hsq hα.le
      dsimp only [m] at this
      nlinarith only [this]
    calc
      _ = ∑ ST ∈ P.nonUniforms G α, a ST.1 * b ST.2 := by
        calc
          _ = ∑ ST ∈ P.nonUniforms G α,
              if ST ∈ P.nonUniforms G α then a ST.1 * b ST.2 else 0 := by
            symm
            apply Finset.sum_subset hNUsub
            intro ST hST hnot
            simp only [hnot, if_false]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro ST hST
            simp only [hST, if_true]
      _ ≤ ∑ ST ∈ P.nonUniforms G α, c ST.1 * c ST.2 := by
        apply Finset.sum_le_sum
        intro ST hST
        exact mul_le_mul (hac ST.1) (hbc ST.2) (hb0 ST.2) (hc0 ST.1)
      _ ≤ _ := hu.le.trans hscale
  have hareaD : (∑ ST ∈ R,
      if ST.1 = ST.2 then a ST.1 * b ST.2 else 0) ≤
      6 / (l : ℝ) * (n : ℝ) ^ 2 := by
    as_aux_lemma =>
    calc
      _ = ∑ S ∈ P.parts, a S * b S := by
        change (∑ ST ∈ P.parts ×ˢ P.parts,
          if ST.1 = ST.2 then a ST.1 * b ST.2 else 0) = _
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro S hS
        simp only [Finset.sum_ite_eq, hS, if_true]
      _ ≤ ∑ S ∈ P.parts, (3 * n / m) * c S := by
        apply Finset.sum_le_sum
        intro S hS
        exact (mul_le_mul (hac S) (hbc S) (hb0 S) (hc0 S)).trans
          (mul_le_mul_of_nonneg_right (hsize S hS) (hc0 S))
      _ = (3 * n / m) * (2 * n) := by rw [← Finset.mul_sum, hc]
      _ = 6 * (n : ℝ) ^ 2 / m := by ring
      _ ≤ 6 * (n : ℝ) ^ 2 / l :=
        div_le_div_of_nonneg_left (by positivity) hlr hml
      _ = _ := by ring
  -- The causes may overlap; their nonnegative indicators overcount the complement.
  have hpoint : ∀ ST ∈ R,
      (if ST ∉ E then a ST.1 * b ST.2 else 0) ≤
        (if ¬γ * c ST.1 ≤ a ST.1 then a ST.1 * b ST.2 else 0) +
        (if ¬γ * c ST.2 ≤ b ST.2 then a ST.1 * b ST.2 else 0) +
        (if ST ∈ P.nonUniforms G α then a ST.1 * b ST.2 else 0) +
        (if ST.1 = ST.2 then a ST.1 * b ST.2 else 0) := by
    intro ST hST
    have hp : ST.1 ∈ P.parts ∧ ST.2 ∈ P.parts := Finset.mem_product.mp hST
    have hweight : 0 ≤ a ST.1 * b ST.2 := mul_nonneg (ha0 _) (hb0 _)
    have hU0 : 0 ≤ (if ¬γ * c ST.1 ≤ a ST.1 then a ST.1 * b ST.2 else 0) := by
      exact ite_nonneg hweight (le_refl 0)
    have hW0 : 0 ≤ (if ¬γ * c ST.2 ≤ b ST.2 then a ST.1 * b ST.2 else 0) := by
      exact ite_nonneg hweight (le_refl 0)
    have hN0 : 0 ≤ (if ST ∈ P.nonUniforms G α then a ST.1 * b ST.2 else 0) := by
      exact ite_nonneg hweight (le_refl 0)
    have hD0 : 0 ≤ (if ST.1 = ST.2 then a ST.1 * b ST.2 else 0) := by
      exact ite_nonneg hweight (le_refl 0)
    by_cases hnot : ST ∉ E
    · rw [if_pos hnot]
      have hcauses : ST.1 = ST.2 ∨ ¬γ * c ST.1 ≤ a ST.1 ∨
          ¬γ * c ST.2 ≤ b ST.2 ∨ ST ∈ P.nonUniforms G α := by
        by_contra h
        push Not at h
        rcases h with ⟨hD, hU, hW, hN⟩
        have huni : G.IsUniform α ST.1 ST.2 := by
          by_contra huni
          exact hN ((P.mk_mem_nonUniforms G).mpr ⟨hp.1, hp.2, hD, huni⟩)
        exact hnot ((hE ST.1 ST.2).mpr ⟨hp.1, hp.2, hD, huni, hU, hW⟩)
      rcases hcauses with hD | hU | hW | hN
      · rw [if_pos hD]
        linarith only [hU0, hW0, hN0]
      · rw [if_pos hU]
        linarith only [hW0, hN0, hD0]
      · rw [if_pos hW]
        linarith only [hU0, hN0, hD0]
      · rw [if_pos hN]
        linarith only [hU0, hW0, hD0]
    · rw [if_neg hnot]
      linarith only [hU0, hW0, hN0, hD0]
  change (∑ ST ∈ R.filter (fun ST => ST ∉ E), a ST.1 * b ST.2) ≤ _
  rw [Finset.sum_filter]
  calc
    _ ≤ ∑ ST ∈ R,
        ((if ¬γ * c ST.1 ≤ a ST.1 then a ST.1 * b ST.2 else 0) +
        (if ¬γ * c ST.2 ≤ b ST.2 then a ST.1 * b ST.2 else 0) +
        (if ST ∈ P.nonUniforms G α then a ST.1 * b ST.2 else 0) +
        (if ST.1 = ST.2 then a ST.1 * b ST.2 else 0)) :=
      Finset.sum_le_sum hpoint
    _ ≤ (4 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith only [hareaU, hareaW, hareaN, hareaD]
