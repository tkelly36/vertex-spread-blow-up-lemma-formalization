import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Density

-- [TABLET NODE: SuperRegularTypicalCore]
theorem SuperRegularTypicalCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U W : Finset V)
    (n : ℕ) (d h : ℝ) (hn : 0 < n) (hh : 0 < h) (hh1 : h < 1)
    (hU : U.card = n) (hW : W.card = n)
    (hrect : ∀ A ⊆ U, ∀ B ⊆ W, h * n < (A.card : ℝ) →
      h * n < (B.card : ℝ) → |(H.edgeDensity A B : ℝ) - d| < h / 2) :
    ∃ U₀ W₀ : Finset V, U₀ ⊆ U ∧ W₀ ⊆ W ∧
      ((U \ U₀).card : ℝ) ≤ 2 * h * n ∧
      ((W \ W₀).card : ℝ) ≤ 2 * h * n ∧
      (∀ u ∈ U₀, (d - 3 * h) * n ≤
        ((W₀.filter fun w => H.Adj u w).card : ℝ) ∧
        ((W₀.filter fun w => H.Adj u w).card : ℝ) ≤ (d + h) * n) ∧
      (∀ w ∈ W₀, (d - 3 * h) * n ≤
        ((U₀.filter fun u => H.Adj u w).card : ℝ) ∧
        ((U₀.filter fun u => H.Adj u w).card : ℝ) ≤ (d + h) * n) := by
-- BODY
  classical
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hhn : h * (n : ℝ) < n := by nlinarith only [hh1, hnr]
  have hcount : ∀ A R : Finset V,
      ((H.interedges A R).card : ℝ) =
        ∑ a ∈ A, ((R.filter fun r => H.Adj a r).card : ℝ) := by
    intro A R
    simp only [SimpleGraph.interedges_def, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  have hdensity : ∀ A R : Finset V, 0 < (A.card : ℝ) → R.card = n →
      (H.edgeDensity A R : ℝ) * ((A.card : ℝ) * n) =
        ((H.interedges A R).card : ℝ) := by
    intro A R hA hR
    simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_mul,
      Rat.cast_natCast, hR]
    exact div_mul_cancel₀ _ (mul_pos hA hnr).ne'
  have typical : ∀ L R : Finset V, L.card = n → R.card = n →
      (∀ A ⊆ L, h * n < (A.card : ℝ) →
        |(H.edgeDensity A R : ℝ) - d| < h / 2) →
      ∃ L₀ : Finset V, L₀ ⊆ L ∧ ((L \ L₀).card : ℝ) ≤ 2 * h * n ∧
        ∀ v ∈ L₀, (d - h) * n ≤ ((R.filter fun w => H.Adj v w).card : ℝ) ∧
          ((R.filter fun w => H.Adj v w).card : ℝ) ≤ (d + h) * n := by
    as_aux_lemma =>
    intro L R _ hR htest
    let low := L.filter fun v => ((R.filter fun w => H.Adj v w).card : ℝ) < (d - h) * n
    let high := L.filter fun v => (d + h) * n < ((R.filter fun w => H.Adj v w).card : ℝ)
    have hlow : (low.card : ℝ) ≤ h * n := by
      by_contra! hlarge
      have hpos : 0 < (low.card : ℝ) := (mul_pos hh hnr).trans hlarge
      have hdens := (abs_lt.mp (htest low (Finset.filter_subset _ _) hlarge)).1
      have hsum : ((H.interedges low R).card : ℝ) ≤
          (d - h) * n * low.card := by
        rw [hcount]
        calc
          _ ≤ ∑ _v ∈ low, (d - h) * n := Finset.sum_le_sum (fun v hv =>
            (Finset.mem_filter.mp hv).2.le)
          _ = _ := by simp [mul_comm]
      have hprod := mul_lt_mul_of_pos_right
        (show d - h / 2 < (H.edgeDensity low R : ℝ) by linarith only [hdens])
        (mul_pos hpos hnr)
      rw [hdensity low R hpos hR] at hprod
      have hgap := mul_pos hh (mul_pos hpos hnr)
      nlinarith only [hsum, hprod, hgap]
    have hhigh : (high.card : ℝ) ≤ h * n := by
      by_contra! hlarge
      have hpos : 0 < (high.card : ℝ) := (mul_pos hh hnr).trans hlarge
      have hdens := (abs_lt.mp (htest high (Finset.filter_subset _ _) hlarge)).2
      have hsum : (d + h) * n * high.card ≤
          ((H.interedges high R).card : ℝ) := by
        rw [hcount]
        calc
          _ = ∑ _v ∈ high, (d + h) * n := by simp [mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
      have hprod := mul_lt_mul_of_pos_right
        (show (H.edgeDensity high R : ℝ) < d + h / 2 by linarith only [hdens])
        (mul_pos hpos hnr)
      rw [hdensity high R hpos hR] at hprod
      have hgap := mul_pos hh (mul_pos hpos hnr)
      nlinarith only [hsum, hprod, hgap]
    let L₀ := L \ (low ∪ high)
    refine ⟨L₀, Finset.sdiff_subset, ?_, ?_⟩
    · have hsub : L \ L₀ ⊆ low ∪ high := by
        intro v hv
        obtain ⟨hvL, hvnot⟩ := Finset.mem_sdiff.mp hv
        by_contra hvbad
        exact hvnot (Finset.mem_sdiff.mpr ⟨hvL, hvbad⟩)
      have hcard : (L \ L₀).card ≤ low.card + high.card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hcardR : ((L \ L₀).card : ℝ) ≤ (low.card : ℝ) + high.card := by
        exact_mod_cast hcard
      linarith only [hcardR, hlow, hhigh]
    · intro v hv
      obtain ⟨hvL, hvnot⟩ := Finset.mem_sdiff.mp hv
      constructor
      · by_contra! hsmall
        exact hvnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvL, hsmall⟩))
      · by_contra! hlarge
        exact hvnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvL, hlarge⟩))
  obtain ⟨U₀, hU₀, hbadU, hfullU⟩ := typical U W hU hW
    (fun A hA hsize => hrect A hA W (by rfl) hsize (by simpa only [hW] using hhn))
  obtain ⟨W₀, hW₀, hbadW, hfullW⟩ := typical W U hW hU (by
    intro B hB hsize
    have ht := hrect U (by rfl) B hB (by simpa only [hU] using hhn) hsize
    simpa only [SimpleGraph.edgeDensity_comm] using ht)
  have deletion : ∀ R R₀ : Finset V, ∀ v : V,
      ((R.filter fun w => H.Adj v w).card : ℝ) ≤
        ((R₀.filter fun w => H.Adj v w).card : ℝ) + (R \ R₀).card := by
    intro R R₀ v
    have hsub : R.filter (fun w => H.Adj v w) ⊆
        (R₀.filter fun w => H.Adj v w) ∪ (R \ R₀) := by
      intro w hw
      obtain ⟨hwR, hvw⟩ := Finset.mem_filter.mp hw
      by_cases hw₀ : w ∈ R₀
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw₀, hvw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwR, hw₀⟩)
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  refine ⟨U₀, W₀, hU₀, hW₀, hbadU, hbadW, ?_, ?_⟩
  · intro u hu
    have hfull := hfullU u hu
    have hloss := deletion W W₀ u
    have hmono : ((W₀.filter fun w => H.Adj u w).card : ℝ) ≤
        ((W.filter fun w => H.Adj u w).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hW₀)
    constructor
    · nlinarith only [hfull.1, hloss, hbadW]
    · exact hmono.trans hfull.2
  · intro w hw
    have hfull := hfullW w hw
    have hloss := deletion U U₀ w
    have hmono : ((U₀.filter fun u => H.Adj u w).card : ℝ) ≤
        ((U.filter fun u => H.Adj w u).card : ℝ) := by
      have heq : U₀.filter (fun u => H.Adj u w) = U₀.filter (fun u => H.Adj w u) := by
        ext u
        simp only [Finset.mem_filter, H.adj_comm]
      rw [heq]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hU₀)
    have heq : U₀.filter (fun u => H.Adj w u) = U₀.filter (fun u => H.Adj u w) := by
      ext u
      simp only [Finset.mem_filter, H.adj_comm]
    rw [heq] at hloss
    constructor
    · nlinarith only [hfull.1, hloss, hbadU]
    · exact hmono.trans hfull.2
