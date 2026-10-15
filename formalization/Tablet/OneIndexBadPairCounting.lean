import Tablet.SuperRegularPair
import Tablet.RegularPairLowerTail
import Tablet.RegularPairUpperTail
import Tablet.CodegreeWindowTransfer
import Tablet.SmallNeighborhoodCodegreeWindow

-- [TABLET NODE: OneIndexBadPairCounting]
theorem OneIndexBadPairCounting :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (F₁₃ F₂₃ : SimpleGraph V)
      [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
      (W₁ W₂ W₃ : Finset V) (n : ℕ) (ε d₁₃ d₂₃ : ENNReal),
      W₁.card = n → W₂.card = n →
      (W₃.card + 1 = n ∨ W₃.card = n ∨ W₃.card = n + 1) → ε ≤ 1 →
      d₁₃ ≤ 1 → d₂₃ ≤ 1 →
      SuperRegularPair F₁₃ W₁ W₃ ε d₁₃ →
      SuperRegularPair F₂₃ W₂ W₃ ε d₂₃ →
      ∀ U ⊆ W₁, ∀ W ⊆ W₂,
        2 * ε ^ (2 : ℝ)⁻¹ * n < U.card →
        2 * ε ^ (2 : ℝ)⁻¹ * n < W.card →
        (((U.product W).filter fun p =>
          ¬ ((d₁₃ * d₂₃ - 2 * ε) * W₃.card ≤
              (((W₃.filter fun z => F₁₃.Adj p.1 z ∧ F₂₃.Adj p.2 z).card : ENNReal)) ∧
            (((W₃.filter fun z => F₁₃.Adj p.1 z ∧ F₂₃.Adj p.2 z).card : ENNReal)) ≤
              (d₁₃ * d₂₃ + 2 * ε) * W₃.card)).card : ENNReal) /
          ((U.card : ENNReal) * (W.card : ENNReal)) ≤
            ε ^ (2 : ℝ)⁻¹ := by
-- BODY
  intro V _ _ F₁₃ F₂₃ _ _ W₁ W₂ W₃ n ε d₁₃ d₂₃
    _hW₁ hW₂ _hnear hε hd₁₃ hd₂₃ hF₁₃ hF₂₃ U hU W hW hsizeU hsizeW
  classical
  by_cases hW₃ : W₃ = ∅
  · simp [hW₃]
  have hk : W₃.card ≠ 0 := by
    intro hkzero
    exact hW₃ (Finset.card_eq_zero.mp hkzero)
  let C (x v : V) := (W₃.filter fun z => F₁₃.Adj x z ∧ F₂₃.Adj v z).card
  let bad (x v : V) := ¬ ((d₁₃ * d₂₃ - 2 * ε) * W₃.card ≤ (C x v : ENNReal) ∧
    (C x v : ENNReal) ≤ (d₁₃ * d₂₃ + 2 * ε) * W₃.card)
  change (((U.product W).filter fun p => bad p.1 p.2).card : ENNReal) /
    ((U.card : ENNReal) * W.card) ≤ ε ^ (2 : ℝ)⁻¹
  have hrow : ∀ x ∈ W₁, ((W₂.filter fun v => bad x v).card : ENNReal) ≤ 2 * ε * n := by
    intro x hx
    let S := W₃.filter fun z => F₁₃.Adj x z
    have hS : S ⊆ W₃ := Finset.filter_subset _ _
    have hSk : S.card ≤ W₃.card := Finset.card_le_card hS
    obtain ⟨halower, haupper⟩ := hF₁₃.2.1 x hx
    change (d₁₃ - ε) * W₃.card ≤ (S.card : ENNReal) at halower
    change (S.card : ENNReal) ≤ (d₁₃ + ε) * W₃.card at haupper
    have hC (v : V) : (S.filter fun z => F₂₃.Adj v z).card = C x v := by
      simp only [S, C, Finset.filter_filter]
    have hca (v : V) : C x v ≤ S.card := by
      rw [← hC v]
      exact Finset.card_filter_le _ _
    by_cases hsmall : (S.card : ENNReal) ≤ ε * W₃.card
    · have hempty : (W₂.filter fun v => bad x v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro v _hv hbad
        exact hbad (SmallNeighborhoodCodegreeWindow ε d₁₃ d₂₃ W₃.card S.card
          (C x v) hk hε hd₁₃ hd₂₃ halower hsmall (hca v))
      simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_le]
    · have hlarge : ε * W₃.card < S.card := lt_of_not_ge hsmall
      let Tminus := W₂.filter fun v =>
        ((S.filter fun z => F₂₃.Adj v z).card : ENNReal) < (d₂₃ - ε) * S.card
      let Tplus := W₂.filter fun v =>
        (d₂₃ + ε) * S.card < ((S.filter fun z => F₂₃.Adj v z).card : ENNReal)
      have hminus : (Tminus.card : ENNReal) ≤ ε * W₂.card :=
        RegularPairLowerTail F₂₃ W₂ W₃ S ε d₂₃ hε hd₂₃ hF₂₃.1 hS hlarge
      have hplus : (Tplus.card : ENNReal) ≤ ε * W₂.card :=
        RegularPairUpperTail F₂₃ W₂ W₃ S ε d₂₃ hε hd₂₃ hF₂₃.1 hS hlarge
      have hsubset : (W₂.filter fun v => bad x v) ⊆ Tminus ∪ Tplus := by
        intro v hv
        obtain ⟨hvW₂, hvbad⟩ := Finset.mem_filter.mp hv
        by_cases hm : v ∈ Tminus
        · exact Finset.mem_union_left _ hm
        by_cases hp : v ∈ Tplus
        · exact Finset.mem_union_right _ hp
        have hlower : (d₂₃ - ε) * S.card ≤ (C x v : ENNReal) := by
          have hnot : ¬ ((S.filter fun z => F₂₃.Adj v z).card : ENNReal) <
              (d₂₃ - ε) * S.card := by
            intro hlt
            exact hm (Finset.mem_filter.mpr ⟨hvW₂, hlt⟩)
          simpa only [hC v] using le_of_not_gt hnot
        have hupper : (C x v : ENNReal) ≤ (d₂₃ + ε) * S.card := by
          have hnot : ¬ (d₂₃ + ε) * S.card <
              ((S.filter fun z => F₂₃.Adj v z).card : ENNReal) := by
            intro hlt
            exact hp (Finset.mem_filter.mpr ⟨hvW₂, hlt⟩)
          simpa only [hC v] using le_of_not_gt hnot
        exact False.elim (hvbad (CodegreeWindowTransfer ε d₁₃ d₂₃ W₃.card S.card
          (C x v) hε hd₁₃ hd₂₃ hSk halower haupper hlower hupper))
      calc
        ((W₂.filter fun v => bad x v).card : ENNReal) ≤ (Tminus ∪ Tplus).card := by
          exact_mod_cast Finset.card_le_card hsubset
        _ ≤ (Tminus.card : ENNReal) + Tplus.card := by
          exact_mod_cast Finset.card_union_le Tminus Tplus
        _ ≤ ε * W₂.card + ε * W₂.card := add_le_add hminus hplus
        _ = 2 * ε * n := by rw [hW₂]; ring
  have hB : (((U.product W).filter fun p => bad p.1 p.2).card : ENNReal) ≤
      (U.card : ENNReal) * (2 * ε * n) := by
    rw [FilteredProductRowCount U W bad, Nat.cast_sum]
    calc
      (∑ x ∈ U, ((W.filter fun v => bad x v).card : ENNReal)) ≤
          ∑ _x ∈ U, 2 * ε * n := by
        apply Finset.sum_le_sum
        intro x hx
        have hrestrict : W.filter (bad x) ⊆ W₂.filter (bad x) :=
          Finset.filter_subset_filter _ hW
        have hcard : ((W.filter (bad x)).card : ENNReal) ≤ (W₂.filter (bad x)).card := by
          exact_mod_cast Finset.card_le_card hrestrict
        exact hcard.trans (hrow x (hU hx))
      _ = (U.card : ENNReal) * (2 * ε * n) := by simp only [Finset.sum_const, nsmul_eq_mul]
  by_cases hzero : ε = 0
  · have hBzero : ((U.product W).filter fun p => bad p.1 p.2).card = 0 := by
      have : (((U.product W).filter fun p => bad p.1 p.2).card : ENNReal) = 0 :=
        le_antisymm (by simpa only [hzero, mul_zero, zero_mul] using hB) (zero_le _)
      exact_mod_cast this
    simp only [hBzero, Nat.cast_zero, ENNReal.zero_div, zero_le]
  have hUzero : (U.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hsizeU)
  have hWzero : (W.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hsizeW)
  have hdenzero : (U.card : ENNReal) * W.card ≠ 0 := mul_ne_zero hUzero hWzero
  have hdenfinite : (U.card : ENNReal) * W.card ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  let s := ε ^ (2 : ℝ)⁻¹
  have hsquare : s * s = ε := by
    dsimp only [s]
    rw [← pow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hscale : 2 * ε * n ≤ s * W.card := by
    calc
      2 * ε * n = s * (2 * s * n) := by rw [← hsquare]; ring
      _ ≤ s * W.card := mul_le_mul_left' hsizeW.le s
  apply (ENNReal.div_le_iff hdenzero hdenfinite).mpr
  calc
    (((U.product W).filter fun p => bad p.1 p.2).card : ENNReal) ≤
        (U.card : ENNReal) * (2 * ε * n) := hB
    _ ≤ (U.card : ENNReal) * (s * W.card) := mul_le_mul_left' hscale _
    _ = s * ((U.card : ENNReal) * W.card) := by ring
