import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter
open scoped Topology

-- [TABLET NODE: ExtractionTailCutoffs]
theorem ExtractionTailCutoffs (c h : ℝ) (M : ℕ) (hc : 0 < c) (hh : 0 < h) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ M ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        1 ≤ h * (n : ℝ) ∧
        4 * n * Real.exp (-c ^ 2 * (n : ℝ) / 8) < 1 / 4 ∧
        2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1 / 4 ∧
        4 * n * Real.exp (-2 * h ^ 2 * (n : ℝ)) < 1 / 4 ∧
        2 * (4 : ℝ) ^ n * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) < 1 / 4 := by
-- BODY
  have linear : ∀ a : ℝ, 0 < a →
      ∀ᶠ n : ℕ in atTop, 4 * n * Real.exp (-a * (n : ℝ)) < 1 / 4 := by
    intro a ha
    have hscale : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop ha
    have hlim : Tendsto (fun n : ℕ => 4 * n * Real.exp (-a * (n : ℝ)))
        atTop (𝓝 0) := by
      have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul
        (4 / a)
      convert ht using 1
      · ext n
        simp only [Function.comp_def, pow_one]
        field_simp
      · simp
    exact hlim.eventually_lt_const (by norm_num)
  have quadratic : ∀ b : ℝ, 0 < b →
      ∀ᶠ n : ℕ in atTop, 2 * (4 : ℝ) ^ n *
        Real.exp (-b * (n : ℝ) ^ 2) < 1 / 4 := by
    intro b hb
    have hlarge : ∀ᶠ n : ℕ in atTop, (Real.log 4 + 1) / b ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    have hlim : Tendsto (fun n : ℕ => 2 * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
    filter_upwards [hlarge, hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)]
      with n hlarge hsmall
    have hlin := (div_le_iff₀ hb).mp hlarge
    have hprod := mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hexp : (n : ℝ) * Real.log 4 - b * (n : ℝ) ^ 2 ≤ -(n : ℝ) := by
      nlinarith only [hprod]
    calc
      2 * (4 : ℝ) ^ n * Real.exp (-b * (n : ℝ) ^ 2)
          = 2 * Real.exp ((n : ℝ) * Real.log 4 - b * (n : ℝ) ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
      _ ≤ 2 * Real.exp (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
      _ < 1 / 4 := hsmall
  have h₁ := linear (c ^ 2 / 8) (by positivity)
  have h₂ := quadratic (h ^ 4 / 8) (by positivity)
  have h₃ := linear (2 * h ^ 2) (by positivity)
  have h₄ := quadratic (2 * h ^ 4) (by positivity)
  have hfloor : ∀ᶠ n : ℕ in atTop, 1 / h ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hall : ∀ᶠ n : ℕ in atTop,
      1 ≤ h * (n : ℝ) ∧
      4 * n * Real.exp (-c ^ 2 * (n : ℝ) / 8) < 1 / 4 ∧
      2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1 / 4 ∧
      4 * n * Real.exp (-2 * h ^ 2 * (n : ℝ)) < 1 / 4 ∧
      2 * (4 : ℝ) ^ n * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) < 1 / 4 := by
    filter_upwards [hfloor, h₁, h₂, h₃, h₄] with n hf h₁ h₂ h₃ h₄
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hf' := (div_le_iff₀ hh).mp hf
      simpa only [mul_comm] using hf'
    · convert h₁ using 1 <;> congr 2 <;> ring
    · convert h₂ using 1 <;> congr 2 <;> ring
    · convert h₃ using 1 <;> congr 2 <;> ring
    · convert h₄ using 1 <;> congr 2 <;> ring
  obtain ⟨N, hN⟩ := hall.exists_forall_of_atTop
  refine ⟨max 1 (max M N), le_max_left _ _,
    (le_max_left M N).trans (le_max_right _ _), ?_⟩
  intro n hn
  exact hN n (((le_max_right M N).trans (le_max_right _ _)).trans hn)
