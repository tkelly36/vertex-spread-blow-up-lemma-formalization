import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- [TABLET NODE: RegularExtractionParameters]
theorem RegularExtractionParameters (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ h γ α ε : ℝ, ∃ l M n₀ : ℕ,
      0 < h ∧ h < η ∧ h ≤ 1 / 100 ∧
      0 < γ ∧ γ ≤ 1 ∧ 0 < α ∧ α ≤ γ ∧ α ≤ γ ^ 2 ∧
      0 < ε ∧ ε < η ∧ ε * M < γ ∧
      1 ≤ l ∧ l ≤ M ∧ SzemerediRegularity.bound α l ≤ M ∧
      1 ≤ n₀ ∧ M ≤ n₀ ∧
      2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2 < h / 4 ∧
      ∀ n : ℕ, n₀ ≤ n →
        2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1 := by
-- BODY
  let h := min (η / 100) (1 / 100 : ℝ)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hh100 : h ≤ 1 / 100 := min_le_right _ _
  have hhη : h < η := (min_le_left _ _).trans_lt (by linarith)
  have hh1 : h ≤ 1 := hh100.trans (by norm_num)
  let γ := h ^ 4 / 100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hpow1 : h ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hh.le hh1 4
  have hγ1 : γ ≤ 1 := by dsimp [γ]; linarith only [hpow1]
  let α := γ ^ 2 / 4
  have hα : 0 < α := by dsimp [α]; positivity
  have hα4 : α ≤ γ / 4 := by dsimp [α]; nlinarith only [hγ1, hγ]
  have hαγ : α ≤ γ := by linarith only [hα4, hγ]
  have hαγγ : α ≤ γ ^ 2 := by dsimp [α]; nlinarith only [sq_nonneg γ]
  let l := Nat.ceil (1 / γ)
  have hl : 1 ≤ l := Nat.one_le_ceil_iff.mpr (by positivity)
  have hlR : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have h1l : 1 / (l : ℝ) ≤ γ := by
    apply (div_le_iff₀ hlR).mpr
    have hc : 1 / γ ≤ (l : ℝ) := Nat.le_ceil _
    have hc' := (div_le_iff₀ hγ).mp hc
    nlinarith only [hc']
  let M := max (max 1 l) (SzemerediRegularity.bound α l)
  have hM1 : 1 ≤ M := (le_max_left 1 l).trans (le_max_left _ _)
  have hlM : l ≤ M := (le_max_right 1 l).trans (le_max_left _ _)
  have hbound : SzemerediRegularity.bound α l ≤ M := le_max_right _ _
  have hMR : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  let ε := min (η / 2) (γ / (2 * M))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεη : ε < η := (min_le_left _ _).trans_lt (by linarith)
  have hεM : ε * M < γ := by
    have he : ε ≤ γ / (2 * M) := min_le_right _ _
    have he' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mp he
    nlinarith only [he', hγ]
  have hmargin : 2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2 < h / 4 := by
    have h6l : 6 / (l : ℝ) ≤ 6 * γ := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left h1l (by norm_num : (0 : ℝ) ≤ 6)
    have hK : 6 * γ + 9 * α + 6 / (l : ℝ) ≤ 15 * γ := by
      linarith only [hα4, h6l, hγ]
    have ha : 2 * α ≤ h ^ 4 / 200 := by
      dsimp [γ] at hα4
      linarith only [hα4]
    have hh2 : h ^ 2 ≤ h / 100 := by nlinarith only [hh100, hh]
    have hh21 : h ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ hh.le hh1 2
    have hh42 : h ^ 4 ≤ h ^ 2 := by nlinarith only [hh21, sq_nonneg h]
    calc
      2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2
          ≤ h ^ 4 / 200 + (15 * γ) / h ^ 2 :=
        add_le_add ha (div_le_div_of_nonneg_right hK (sq_nonneg h))
      _ = h ^ 4 / 200 + 15 * h ^ 2 / 100 := by
        dsimp [γ]
        field_simp
      _ ≤ 31 * h ^ 2 / 200 := by nlinarith only [hh42]
      _ < h / 4 := by nlinarith only [hh2, hh]
  let N := Nat.ceil (16 * Real.log 4 / h ^ 4)
  let n₀ := max M (max 1 N)
  have hn₀ : 1 ≤ n₀ := (le_max_left 1 N).trans (le_max_right _ _)
  have hMn₀ : M ≤ n₀ := le_max_left _ _
  refine ⟨h, γ, α, ε, l, M, n₀, hh, hhη, hh100, hγ, hγ1,
    hα, hαγ, hαγγ, hε, hεη, hεM, hl, hlM, hbound, hn₀, hMn₀, hmargin, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn₀.trans hn
  have hNn : N ≤ n := ((le_max_right 1 N).trans (le_max_right M _)).trans hn
  have hceil : 16 * Real.log 4 / h ^ 4 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNn)
  have hgrowth := (div_le_iff₀ (by positivity : (0 : ℝ) < h ^ 4)).mp hceil
  have hmul := mul_le_mul_of_nonneg_right hgrowth (by positivity : (0 : ℝ) ≤ n)
  have hlin : (n : ℝ) * Real.log 4 ≤ h ^ 4 * (n : ℝ) ^ 2 / 16 := by
    nlinarith only [hmul]
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  have hmul2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ h ^ 4)
  have hquad : Real.log 4 ≤ h ^ 4 * (n : ℝ) ^ 2 / 16 := by
    nlinarith only [hgrowth, hmul2]
  calc
    2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8)
        = 2 * Real.exp ((n : ℝ) * Real.log 4 - h ^ 4 * (n : ℝ) ^ 2 / 8) := by
      rw [show -h ^ 4 * (n : ℝ) ^ 2 / 8 = -(h ^ 4 * (n : ℝ) ^ 2 / 8) by ring,
        sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact mul_assoc _ _ _
    _ ≤ 2 * Real.exp (-Real.log 4) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      linarith only [hlin, hquad]
    _ < 1 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
