import Tablet.MatchingConcentrationCorrection
import Mathlib.Topology.Order.Basic

-- [TABLET NODE: MatchingConcentrationCorrectionAbsorption]
theorem MatchingConcentrationCorrectionAbsorption (d : ℝ) (hd : 0 < d)
    (hd1 : d ≤ 1) :
    Filter.Tendsto (MatchingConcentrationCorrection d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    ∀ γ : ℝ, 0 < γ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 16 ∧ ε₀ < d / 4 ∧
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        MatchingConcentrationCorrection d ε ≤ γ ∧
        ∀ n : ℕ, n₀ ≤ n →
          2 * Real.exp ((n : ℝ) * (MatchingConcentrationCorrection d ε - 2 * γ)) ≤
            Real.exp (-γ / 2) ^ n := by
-- BODY
  have hD : ContinuousAt (fun e : ℝ => d + e + 3 * Real.sqrt e) 0 := by fun_prop
  have hden : ContinuousAt (fun e : ℝ => d - 2 * e) 0 := by fun_prop
  have hquot := hD.div hden (by simpa using hd.ne')
  have hlog := hquot.log (by simp [hd.ne'])
  have hmin := hD.min (continuousAt_const (y := (1 : ℝ)))
  have hminlog := hmin.log (by simpa [min_eq_left hd1] using hd.ne')
  have hcont : ContinuousAt (MatchingConcentrationCorrection d) 0 :=
    hlog.sub (((continuousAt_const (y := (3 : ℝ))).mul
      Real.continuous_sqrt.continuousAt).mul hminlog)
  have hzero : MatchingConcentrationCorrection d 0 = 0 := by
    simp [MatchingConcentrationCorrection, hd.ne']
  refine ⟨?_, ?_⟩
  · simpa only [hzero] using hcont.continuousWithinAt.tendsto
  · intro γ hγ
    obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp hcont γ hγ
    let ε₀ := min (r / 2) (min (1 / 32) (d / 8))
    have hε₀ : 0 < ε₀ := by
      dsimp [ε₀]
      exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hεr : ε₀ ≤ r / 2 := min_le_left _ _
    have hεsmall : ε₀ ≤ 1 / 32 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hεd : ε₀ ≤ d / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log 2 / γ)
    refine ⟨ε₀, hε₀, by linarith, by linarith, N + 1, by omega, ?_⟩
    intro ε hε hεle
    have hL : MatchingConcentrationCorrection d ε ≤ γ := by
      have hdist : dist ε 0 < r := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hε]
        linarith
      have hbound := hnear hdist
      rw [hzero, Real.dist_eq, sub_zero] at hbound
      exact le_trans (le_abs_self _) hbound.le
    refine ⟨hL, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ n := by
      exact_mod_cast le_trans (Nat.le_succ N) hn
    have hlarge : Real.log 2 ≤ γ * (n : ℝ) / 2 := by
      have hfrac := lt_of_lt_of_le hN hNn
      have hmul := (div_lt_iff₀ hγ).mp hfrac
      linarith
    have htwo : (2 : ℝ) ≤ Real.exp (γ * (n : ℝ) / 2) := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlarge
    calc
      _ ≤ 2 * Real.exp (-(γ * (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      _ ≤ Real.exp (γ * (n : ℝ) / 2) * Real.exp (-(γ * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-γ / 2) ^ n := by
        rw [← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
