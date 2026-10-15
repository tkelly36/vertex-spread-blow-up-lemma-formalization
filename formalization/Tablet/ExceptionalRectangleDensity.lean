import Tablet.PairDensityReal

-- [TABLET NODE: ExceptionalRectangleDensity]
theorem ExceptionalRectangleDensity
    {V : Type*} [DecidableEq V]
    (F G : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel G.Adj]
    (U W U₀ W₀ : Finset V) (n : ℕ) (c h η : ℝ)
    (hc : 0 < c) (hc1 : c < 1) (hh : 0 < h) (hhc : h ≤ c / 100)
    (hη : 0 < η) (h3 : 3 * h < η)
    (hbudget : 2 * h + 4 * h / η < η) (hn : 0 < n)
    (hbadU : ((U \ U₀).card : ℝ) ≤ 2 * h * n)
    (hbadW : ((W \ W₀).card : ℝ) ≤ 2 * h * n)
    (hagree : ∀ u ∈ U₀, ∀ w ∈ W₀, G.Adj u w ↔ F.Adj u w)
    (hrect : ∀ A ⊆ U₀, ∀ B ⊆ W₀, h * n < (A.card : ℝ) →
      h * n < (B.card : ℝ) → |(F.edgeDensity A B : ℝ) - c| ≤ 2 * h) :
    ∀ X ⊆ U, ∀ Y ⊆ W, η * n < (X.card : ℝ) →
      η * n < (Y.card : ℝ) → |(G.edgeDensity X Y : ℝ) - c| < η := by
-- BODY
  classical
  intro X hXU Y hYW hX hY
  let X₀ := X ∩ U₀
  let Y₀ := Y ∩ W₀
  have hX₀X : X₀ ⊆ X := Finset.inter_subset_left
  have hY₀Y : Y₀ ⊆ Y := Finset.inter_subset_left
  have hX₀U : X₀ ⊆ U₀ := Finset.inter_subset_right
  have hY₀W : Y₀ ⊆ W₀ := Finset.inter_subset_right
  have hdx : (X.card : ℝ) - X₀.card ≤ 2 * h * n := by
    have hs : X \ U₀ ⊆ U \ U₀ := Finset.sdiff_subset_sdiff hXU (Finset.Subset.refl _)
    have he : ((X \ U₀).card : ℝ) + X₀.card = X.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter X U₀
    have hl : ((X \ U₀).card : ℝ) ≤ (U \ U₀).card := by
      exact_mod_cast Finset.card_le_card hs
    linarith only [he, hl, hbadU]
  have hdy : (Y.card : ℝ) - Y₀.card ≤ 2 * h * n := by
    have hs : Y \ W₀ ⊆ W \ W₀ := Finset.sdiff_subset_sdiff hYW (Finset.Subset.refl _)
    have he : ((Y \ W₀).card : ℝ) + Y₀.card = Y.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter Y W₀
    have hl : ((Y \ W₀).card : ℝ) ≤ (W \ W₀).card := by
      exact_mod_cast Finset.card_le_card hs
    linarith only [he, hl, hbadW]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : h * n < (X₀.card : ℝ) := by
    nlinarith only [hdx, hX, mul_pos (sub_pos.mpr h3) hnR]
  have hy0 : h * n < (Y₀.card : ℝ) := by
    nlinarith only [hdy, hY, mul_pos (sub_pos.mpr h3) hnR]
  have hxpos : (0 : ℝ) < X.card := lt_trans (mul_pos hη hnR) hX
  have hypos : (0 : ℝ) < Y.card := lt_trans (mul_pos hη hnR) hY
  have hx0pos : (0 : ℝ) < X₀.card := lt_trans (mul_pos hh hnR) hx0
  have hy0pos : (0 : ℝ) < Y₀.card := lt_trans (mul_pos hh hnR) hy0
  have hxne : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hxpos)
  have hyne : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hypos)
  have hx0ne : X₀.Nonempty := Finset.card_pos.mp (by exact_mod_cast hx0pos)
  have hy0ne : Y₀.Nonempty := Finset.card_pos.mp (by exact_mod_cast hy0pos)
  let P := X.product Y
  let Q := X₀.product Y₀
  let E := P.filter fun e => G.Adj e.1 e.2
  let E₀ := Q.filter fun e => F.Adj e.1 e.2
  have hQP : Q ⊆ P := Finset.product_subset_product hX₀X hY₀Y
  have hE₀E : E₀ ⊆ E := by
    intro e he
    obtain ⟨heQ, hf⟩ := Finset.mem_filter.mp he
    obtain ⟨heX, heY⟩ := Finset.mem_product.mp heQ
    exact Finset.mem_filter.mpr ⟨hQP heQ,
      (hagree e.1 (hX₀U heX) e.2 (hY₀W heY)).mpr hf⟩
  have hEsub : E ⊆ E₀ ∪ (P \ Q) := by
    intro e he
    obtain ⟨heP, hg⟩ := Finset.mem_filter.mp he
    by_cases heQ : e ∈ Q
    · obtain ⟨heX, heY⟩ := Finset.mem_product.mp heQ
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heQ,
        (hagree e.1 (hX₀U heX) e.2 (hY₀W heY)).mp hg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨heP, heQ⟩)
  have helo : (E₀.card : ℝ) ≤ E.card := by exact_mod_cast Finset.card_le_card hE₀E
  have hehi : (E.card : ℝ) ≤ E₀.card + (P \ Q).card := by
    exact_mod_cast (Finset.card_le_card hEsub).trans (Finset.card_union_le _ _)
  have hr : ((P \ Q).card : ℝ) =
      (X.card : ℝ) * Y.card - (X₀.card : ℝ) * Y₀.card := by
    have he := Finset.card_sdiff_add_card_eq_card hQP
    have heR : ((P \ Q).card : ℝ) + Q.card = P.card := by exact_mod_cast he
    have hp : (P.card : ℝ) = (X.card : ℝ) * Y.card := by simp [P]
    have hq : (Q.card : ℝ) = (X₀.card : ℝ) * Y₀.card := by simp [Q]
    linarith only [heR, hp, hq]
  have hxle : (X₀.card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card hX₀X
  have hyle : (Y₀.card : ℝ) ≤ Y.card := by exact_mod_cast Finset.card_le_card hY₀Y
  have hrbound : ((P \ Q).card : ℝ) ≤ 2 * h * n * ((X.card : ℝ) + Y.card) := by
    have ha := mul_le_mul_of_nonneg_right hdx hypos.le
    have hb := mul_le_mul_of_nonneg_right hdy hxpos.le
    have hab := mul_nonneg (sub_nonneg.mpr hxle) (sub_nonneg.mpr hyle)
    nlinarith only [hr, ha, hb, hab]
  have hTa : 2 * h * n ≤ (2 * h / η) * X.card := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hη).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hX.le (by positivity : 0 ≤ 2 * h)]
  have hTb : 2 * h * n ≤ (2 * h / η) * Y.card := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hη).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hY.le (by positivity : 0 ≤ 2 * h)]
  have hrsmall : ((P \ Q).card : ℝ) ≤ (4 * h / η) * ((X.card : ℝ) * Y.card) := by
    have ha := mul_le_mul_of_nonneg_right hTa hypos.le
    have hb := mul_le_mul_of_nonneg_right hTb hxpos.le
    have he : 4 * h / η = 2 * (2 * h / η) := by ring
    rw [he]
    nlinarith only [hrbound, ha, hb]
  obtain ⟨_, _, hdcore⟩ := PairDensityReal F X₀ Y₀ hx0ne hy0ne
  have hcore := abs_le.mp (hrect X₀ hX₀U Y₀ hY₀W hx0 hy0)
  rw [hdcore] at hcore
  change -(2 * h) ≤ (E₀.card : ℝ) / ((X₀.card : ℝ) * Y₀.card) - c ∧
    (E₀.card : ℝ) / ((X₀.card : ℝ) * Y₀.card) - c ≤ 2 * h at hcore
  have hden0 : 0 < (X₀.card : ℝ) * Y₀.card := mul_pos hx0pos hy0pos
  have hclo : (c - 2 * h) * ((X₀.card : ℝ) * Y₀.card) ≤ E₀.card :=
    (le_div_iff₀ hden0).mp (by linarith only [hcore.1])
  have hchi : (E₀.card : ℝ) ≤ (c + 2 * h) * ((X₀.card : ℝ) * Y₀.card) :=
    (div_le_iff₀ hden0).mp (by linarith only [hcore.2])
  have hc2 : 0 < c - 2 * h := by linarith only [hc, hhc]
  have hc21 : c - 2 * h < 1 := by linarith only [hc1, hh]
  have hrpos : (0 : ℝ) ≤ (P \ Q).card := by positivity
  have hprodle : (X₀.card : ℝ) * Y₀.card ≤ (X.card : ℝ) * Y.card :=
    mul_le_mul hxle hyle hy0pos.le hxpos.le
  have hlow : (c - 2 * h - 4 * h / η) * ((X.card : ℝ) * Y.card) ≤ E.card := by
    have ht : (c - 2 * h) * ((X.card : ℝ) * Y.card) -
        (c - 2 * h) * ((X₀.card : ℝ) * Y₀.card) ≤ (P \ Q).card := by
      calc
        _ = (c - 2 * h) * ((P \ Q).card : ℝ) := by rw [hr]; ring
        _ ≤ (P \ Q).card := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc21.le hrpos
    nlinarith only [helo, hclo, hrsmall, ht]
  have hhigh : (E.card : ℝ) ≤ (c + 2 * h + 4 * h / η) * ((X.card : ℝ) * Y.card) := by
    have ht := mul_le_mul_of_nonneg_left hprodle (by positivity : 0 ≤ c + 2 * h)
    nlinarith only [hehi, hchi, hrsmall, ht]
  obtain ⟨_, _, hd⟩ := PairDensityReal G X Y hxne hyne
  rw [hd]
  change |(E.card : ℝ) / ((X.card : ℝ) * Y.card) - c| < η
  have hden : 0 < (X.card : ℝ) * Y.card := mul_pos hxpos hypos
  have hlo := (le_div_iff₀ hden).mpr hlow
  have hhi := (div_le_iff₀ hden).mpr hhigh
  exact abs_lt.mpr ⟨by linarith only [hlo, hbudget], by linarith only [hhi, hbudget]⟩
