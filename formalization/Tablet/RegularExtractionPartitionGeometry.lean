import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Tablet.RegularExtractionIneligibleArea

-- [TABLET NODE: RegularExtractionPartitionGeometry]
theorem RegularExtractionPartitionGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (n l M : ℕ) (ε d γ α : ℝ)
    (hU : U.card = n) (hW : W.card = n) (hUW : Disjoint U W)
    (hcover : U ∪ W = Finset.univ) (hl : 1 ≤ l) (hn : M ≤ n)
    (hε : 0 < ε) (hd : 0 < d) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hα : 0 < α) (hαγ : α ≤ γ) (hαγγ : α ≤ γ ^ 2)
    (hεM : ε * M < γ)
    (hlower : ∀ A ⊆ U, ∀ B ⊆ W,
      ε * n < (A.card : ℝ) → ε * n < (B.card : ℝ) →
      d ≤ (G.edgeDensity A B : ℝ))
    (P : Finpartition (Finset.univ : Finset V))
    (heq : P.IsEquipartition) (hlP : l ≤ P.parts.card)
    (hPM : P.parts.card ≤ M) (hunif : P.IsUniform G α) :
    (∀ S ∈ P.parts, (n : ℝ) / P.parts.card ≤ S.card ∧
      (S.card : ℝ) ≤ 3 * n / P.parts.card) ∧
    ∃ E : Finset (Finset V × Finset V),
      E ⊆ P.parts.product P.parts ∧
      (∀ S ∈ P.parts, ∀ T ∈ P.parts,
        (S, T) ∈ E ↔ S ≠ T ∧ G.IsUniform α S T ∧
          γ * S.card ≤ ((U ∩ S).card : ℝ) ∧
          γ * T.card ≤ ((W ∩ T).card : ℝ)) ∧
      (∀ S T, (S, T) ∈ E →
        d ≤ (G.edgeDensity (U ∩ S) (W ∩ T) : ℝ) ∧
        (G.edgeDensity (U ∩ S) (W ∩ T) : ℝ) ≤ 1) ∧
      (∀ S T, (S, T) ∈ E → ∀ A ⊆ U ∩ S, ∀ B ⊆ W ∩ T,
        γ * (U ∩ S).card < (A.card : ℝ) →
        γ * (W ∩ T).card < (B.card : ℝ) →
        |(G.edgeDensity A B : ℝ) - G.edgeDensity (U ∩ S) (W ∩ T)| < 2 * α) ∧
      (∑ ST ∈ (P.parts.product P.parts).filter (fun ST => ST ∉ E),
        (((U ∩ ST.1).card : ℝ) * (W ∩ ST.2).card)) ≤
        (4 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2 := by
-- BODY
  classical
  let m := P.parts.card
  have hm : 0 < m := lt_of_lt_of_le (by omega : 0 < l) hlP
  have hmn : m ≤ n := hPM.trans hn
  have hn0 : 0 < n := hm.trans_le hmn
  have hmr : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hml : (l : ℝ) ≤ m := Nat.cast_le.mpr hlP
  have hmnr : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hlr : 0 < (l : ℝ) := Nat.cast_pos.mpr (by omega)
  have htotal : (Finset.univ : Finset V).card = 2 * n := by
    rw [← hcover, Finset.card_union_of_disjoint hUW, hU, hW]
    omega
  have hsum : (∑ S ∈ P.parts, (S.card : ℝ)) = 2 * n := by
    exact_mod_cast P.sum_card_parts.trans htotal
  have hsize : ∀ S ∈ P.parts, (n : ℝ) / m ≤ S.card ∧
      (S.card : ℝ) ≤ 3 * n / m := by
    as_aux_lemma =>
    intro S hS
    have hlo : (2 * n : ℝ) ≤ m * ((S.card : ℝ) + 1) := by
      calc
        _ = ∑ T ∈ P.parts, (T.card : ℝ) := hsum.symm
        _ ≤ ∑ T ∈ P.parts, ((S.card : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro T hT
          exact_mod_cast (heq hT hS)
        _ = _ := by simp [m, mul_add]
    have hhi : (m : ℝ) * S.card ≤ 2 * n + m := by
      calc
        _ = ∑ T ∈ P.parts, (S.card : ℝ) := by simp [m]
        _ ≤ ∑ T ∈ P.parts, ((T.card : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro T hT
          exact_mod_cast (heq hS hT)
        _ = _ := by rw [Finset.sum_add_distrib, hsum]; simp [m]
    constructor
    · apply (div_le_iff₀ hmr).mpr
      nlinarith only [hlo, hmnr]
    · apply (le_div_iff₀ hmr).mpr
      nlinarith only [hhi, hmnr]
  refine ⟨hsize, ?_⟩
  let E := (P.parts.product P.parts).filter (fun ST =>
    ST.1 ≠ ST.2 ∧ G.IsUniform α ST.1 ST.2 ∧
      γ * ST.1.card ≤ ((U ∩ ST.1).card : ℝ) ∧
      γ * ST.2.card ≤ ((W ∩ ST.2).card : ℝ))
  have hE : ∀ S T, (S, T) ∈ E ↔
      S ∈ P.parts ∧ T ∈ P.parts ∧ S ≠ T ∧ G.IsUniform α S T ∧
      γ * S.card ≤ ((U ∩ S).card : ℝ) ∧
      γ * T.card ≤ ((W ∩ T).card : ℝ) := by
    intro S T
    simp only [E, Finset.mem_filter]
    have hp : (S, T) ∈ P.parts.product P.parts ↔ S ∈ P.parts ∧ T ∈ P.parts :=
      Finset.mem_product
    rw [hp]
    tauto
  have hchunk : ∀ S ∈ P.parts, ∀ X : Finset V,
      γ * S.card ≤ (X.card : ℝ) → ε * n < (X.card : ℝ) := by
    as_aux_lemma =>
    intro S hS X hX
    have hεm : ε * m < γ := by
      calc
        ε * m ≤ ε * M := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hPM) hε.le
        _ < γ := hεM
    have hprod := mul_lt_mul_of_pos_right hεm hnr
    have hbase := mul_le_mul_of_nonneg_left (hsize S hS).1 hγ.le
    have hn_div : (n : ℝ) / m * m = n := div_mul_cancel₀ _ hmr.ne'
    have hscaled := mul_le_mul_of_nonneg_right (hbase.trans hX) hmr.le
    rw [mul_assoc, hn_div] at hscaled
    have hlt : ε * n * m < (X.card : ℝ) * m := by
      nlinarith only [hprod, hscaled]
    exact (mul_lt_mul_iff_of_pos_right hmr).mp hlt
  refine ⟨E, Finset.filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro S hS T hT
    rw [hE]
    simp only [hS, hT, true_and]
  · intro S T hST
    rcases (hE S T).mp hST with ⟨hS, hT, -, -, hUS, hWT⟩
    refine ⟨hlower _ Finset.inter_subset_left _ Finset.inter_subset_left
      (hchunk S hS _ hUS) (hchunk T hT _ hWT), ?_⟩
    exact_mod_cast G.edgeDensity_le_one (U ∩ S) (W ∩ T)
  · intro S T hST A hA B hB hAc hBc
    rcases (hE S T).mp hST with ⟨hS, hT, -, hSTu, hUS, hWT⟩
    have hSc : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    have hAα : (S.card : ℝ) * α ≤ A.card := by
      have h₁ := mul_le_mul_of_nonneg_left hUS hγ.le
      have h₂ := mul_le_mul_of_nonneg_right hαγγ hSc
      nlinarith only [h₁, h₂, hAc]
    have hBα : (T.card : ℝ) * α ≤ B.card := by
      have h₁ := mul_le_mul_of_nonneg_left hWT hγ.le
      have h₂ := mul_le_mul_of_nonneg_right hαγγ hTc
      nlinarith only [h₁, h₂, hBc]
    have hUSα : (S.card : ℝ) * α ≤ (U ∩ S).card := by
      have := mul_le_mul_of_nonneg_right hαγ hSc
      linarith only [this, hUS]
    have hWTα : (T.card : ℝ) * α ≤ (W ∩ T).card := by
      have := mul_le_mul_of_nonneg_right hαγ hTc
      linarith only [this, hWT]
    have h₁ := hSTu (hA.trans Finset.inter_subset_right)
      (hB.trans Finset.inter_subset_right) hAα hBα
    have h₂ := hSTu Finset.inter_subset_right Finset.inter_subset_right hUSα hWTα
    calc
      _ ≤ |(G.edgeDensity A B : ℝ) - G.edgeDensity S T| +
          |(G.edgeDensity S T : ℝ) - G.edgeDensity (U ∩ S) (W ∩ T)| :=
        abs_sub_le _ _ _
      _ < 2 * α := by rw [abs_sub_comm (G.edgeDensity S T : ℝ)]; linarith only [h₁, h₂]
  · exact RegularExtractionIneligibleArea G U W n l γ α hU hW hl hγ hα P
      heq hlP hmn htotal hunif (fun S hS => (hsize S hS).2) E hE
