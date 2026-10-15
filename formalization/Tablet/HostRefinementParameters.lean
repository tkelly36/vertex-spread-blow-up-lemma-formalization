import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter
open scoped Topology

-- [TABLET NODE: HostRefinementParameters]
theorem HostRefinementParameters (k N : ℕ) (η θ : ℝ)
    (hk : 1 ≤ k) (hη : 0 < η) (hη1 : η < 1) (hθ : 0 < θ) :
    ∃ e : ℝ, 0 < e ∧ e < η ∧ e < 1 ∧ e < 1 / (8 * (k : ℝ) ^ 2) ∧
      (4 * (k : ℝ) ^ 2 + 2) * e ≤ θ ∧ 2 * k * e ≤ θ ∧
      ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        2 * k ≤ n ∧ N ≤ n / k ∧
        2 * (r : ℝ) * k * (r + 1) * n *
          Real.exp (-((e / (2 * k)) ^ 2 / (2 * (1 + e / (6 * k)))) * n) < 1 := by
-- BODY
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith only [hkR]
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
  let e := min (η / 2) (min (θ / (8 * (k : ℝ) ^ 2)) (1 / (16 * (k : ℝ) ^ 2)))
  have he : 0 < e := by dsimp [e]; positivity
  have heη : e ≤ η / 2 := min_le_left _ _
  have heθ : e ≤ θ / (8 * (k : ℝ) ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hek : e ≤ 1 / (16 * (k : ℝ) ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heθ' : e * (8 * (k : ℝ) ^ 2) ≤ θ :=
    (le_div_iff₀ (by positivity)).mp heθ
  have hek' : e * (16 * (k : ℝ) ^ 2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hek
  have hcoef : 2 * (k : ℝ) ≤ 8 * (k : ℝ) ^ 2 := by
    nlinarith only [hkR]
  have heη' : e < η := by linarith only [heη, hη]
  refine ⟨e, he, heη', heη'.trans hη1, ?_, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [hek', he, hk2]
  · nlinarith only [heθ', he, hk2]
  · have hmul := mul_le_mul_of_nonneg_right hcoef he.le
    nlinarith only [hmul, heθ']
  intro r
  let c := (e / (2 * (k : ℝ))) ^ 2 / (2 * (1 + e / (6 * k)))
  have hc : 0 < c := by dsimp [c]; positivity
  have hscale : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlim : Tendsto (fun n : ℕ =>
      2 * (r : ℝ) * k * (r + 1) * n * Real.exp (-c * n)) atTop (𝓝 0) := by
    have ht := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale).const_mul
      (2 * (r : ℝ) * k * (r + 1) / c)
    convert ht using 1
    · ext n
      simp only [Function.comp_def, pow_one]
      field_simp
    · simp
  obtain ⟨M, hM⟩ := (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists_forall_of_atTop
  refine ⟨max (2 * k) (max (k * N) M), ?_⟩
  intro n hn
  have hn2 : 2 * k ≤ n := (le_max_left _ _).trans hn
  have hnN : k * N ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : M ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨hn2, (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr ?_, hM n hnM⟩
  simpa only [Nat.mul_comm] using hnN
