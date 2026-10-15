import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- [TABLET NODE: NearEqualRetentionThreshold]
theorem NearEqualRetentionThreshold (ξ h : ℝ) (hξ : 0 < ξ) (hh : 0 < h) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ a b : ℕ,
      n₀ ≤ a → n₀ ≤ b → a ≤ b + 1 → b ≤ a + 1 →
      ENNReal.ofReal
        (2 * (a + b : ℝ) * Real.exp (-2 * ξ ^ 2 * min (a : ℝ) b) +
         2 * (2 : ℝ) ^ (a + b) * Real.exp (-2 * ξ ^ 2 * h ^ 2 * a * b)) < 1 := by
-- BODY
  let k : ℝ := 2 * ξ ^ 2
  let c : ℝ := k * h ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp (x : ℝ) (hx : 0 < x) (j : ℕ) :
      Real.exp (-x) ≤ (j.factorial : ℝ) / x ^ j := by
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
    have hp : 0 < x ^ j / (j.factorial : ℝ) := div_pos (pow_pos hx _) hf
    rw [Real.exp_neg, ← one_div]
    calc
      1 / Real.exp x ≤ 1 / (x ^ j / (j.factorial : ℝ)) :=
        one_div_le_one_div_of_le hp (Real.pow_div_factorial_le_exp x hx.le j)
      _ = (j.factorial : ℝ) / x ^ j := by rw [one_div_div]
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max 1 (max (Real.sqrt (72 / k ^ 3)) (max (4 * Real.log 2 / c) (8 / c))))
  refine ⟨m + 1, by omega, ?_⟩
  intro a b ha hb hab hba
  let s : ℝ := min (a : ℝ) (b : ℝ)
  have hms : (m : ℝ) < s := by
    have ham : m + 1 ≤ a := ha
    have hbm : m + 1 ≤ b := hb
    have ham' : (m : ℝ) + 1 ≤ a := by exact_mod_cast ham
    have hbm' : (m : ℝ) + 1 ≤ b := by exact_mod_cast hbm
    exact lt_min (by linarith only [ham']) (by linarith only [hbm'])
  have hthreshold :
      max 1 (max (Real.sqrt (72 / k ^ 3)) (max (4 * Real.log 2 / c) (8 / c))) < s :=
    hm.trans hms
  have hs1 : 1 ≤ s := (lt_of_le_of_lt (le_max_left _ _) hthreshold).le
  have hs : 0 < s := by linarith only [hs1]
  have hsroot : Real.sqrt (72 / k ^ 3) < s :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hthreshold
  have hslog : 4 * Real.log 2 / c < s :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      hthreshold
  have hs8 : 8 / c < s :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      hthreshold
  have hsa : s ≤ (a : ℝ) := min_le_left _ _
  have hsb : s ≤ (b : ℝ) := min_le_right _ _
  have hab' : (a : ℝ) ≤ b + 1 := by exact_mod_cast hab
  have hba' : (b : ℝ) ≤ a + 1 := by exact_mod_cast hba
  have hsum : (a : ℝ) + b ≤ 2 * s + 1 := by
    dsimp [s]
    rcases le_total (a : ℝ) (b : ℝ) with hle | hle
    · rw [min_eq_left hle]; linarith only [hba']
    · rw [min_eq_right hle]; linarith only [hab']
  have hprod : s ^ 2 ≤ (a : ℝ) * b := by
    calc
      s ^ 2 = s * s := by ring
      _ ≤ (a : ℝ) * b := mul_le_mul hsa hsb hs.le (by positivity)
  have hks : 0 < k * s := mul_pos hk hs
  have hdegree :
      2 * ((a : ℝ) + b) * Real.exp (-k * s) ≤ 36 / (k ^ 3 * s ^ 2) := by
    calc
      2 * ((a : ℝ) + b) * Real.exp (-k * s) ≤
          (6 * s) * Real.exp (-(k * s)) := by
        have : 2 * ((a : ℝ) + b) ≤ 6 * s := by linarith only [hsum, hs1]
        simpa only [neg_mul] using mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ ≤ (6 * s) * (6 / (k * s) ^ 3) := by
        simpa using mul_le_mul_of_nonneg_left (hexp (k * s) hks 3) (by positivity)
      _ = 36 / (k ^ 3 * s ^ 2) := by
        field_simp
        ring
  have hk3 : 0 < k ^ 3 := pow_pos hk _
  have hdegreeDen : 72 < k ^ 3 * s ^ 2 := by
    have hsq : 72 / k ^ 3 < s ^ 2 :=
      (Real.sqrt_lt (by positivity) hs.le).mp hsroot
    simpa only [mul_comm] using (div_lt_iff₀ hk3).mp hsq
  have hdegreeHalf : 36 / (k ^ 3 * s ^ 2) < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < k ^ 3 * s ^ 2)]
    linarith only [hdegreeDen]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogbound : 2 * s * Real.log 2 ≤ c * s ^ 2 / 2 := by
    have hcs : 4 * Real.log 2 < s * c := (div_lt_iff₀ hc).mp hslog
    have hmul := mul_le_mul_of_nonneg_left hcs.le hs.le
    nlinarith only [hmul]
  have hpower : (2 : ℝ) ^ (a + b) = Real.exp (((a : ℝ) + b) * Real.log 2) := by
    rw [← Nat.cast_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hrectangleExp :
      2 * (2 : ℝ) ^ (a + b) * Real.exp (-c * a * b) ≤
        4 * Real.exp (-(c * s ^ 2 / 2)) := by
    rw [hpower]
    calc
      2 * Real.exp (((a : ℝ) + b) * Real.log 2) * Real.exp (-c * a * b) =
          2 * Real.exp (((a : ℝ) + b) * Real.log 2 - c * a * b) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * Real.exp (Real.log 2 - c * s ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have hsumlog := mul_le_mul_of_nonneg_right hsum hlog
        have hprod' := mul_le_mul_of_nonneg_left hprod hc.le
        nlinarith only [hsumlog, hprod', hlogbound]
      _ = 4 * Real.exp (-(c * s ^ 2 / 2)) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]
        ring
  have hrectangle :
      2 * (2 : ℝ) ^ (a + b) * Real.exp (-c * a * b) ≤ 32 / (c ^ 2 * s ^ 4) := by
    calc
      _ ≤ 4 * Real.exp (-(c * s ^ 2 / 2)) := hrectangleExp
      _ ≤ 4 * (2 / (c * s ^ 2 / 2) ^ 2) := by
        simpa using mul_le_mul_of_nonneg_left
          (hexp (c * s ^ 2 / 2) (by positivity) 2) (by norm_num : (0 : ℝ) ≤ 4)
      _ = 32 / (c ^ 2 * s ^ 4) := by
        field_simp
        ring
  have hrectangleDen : 64 < c ^ 2 * s ^ 4 := by
    have hcs : 8 < s * c := (div_lt_iff₀ hc).mp hs8
    have hsq : 64 < (s * c) ^ 2 := by nlinarith only [hcs, sq_nonneg (s * c - 8)]
    have hs2 : 1 ≤ s ^ 2 := by nlinarith only [hs1, sq_nonneg (s - 1)]
    have hmore : (s * c) ^ 2 ≤ (s * c) ^ 2 * s ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) hs2
    nlinarith only [hsq, hmore]
  have hrectangleHalf : 32 / (c ^ 2 * s ^ 4) < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < c ^ 2 * s ^ 4)]
    linarith only [hrectangleDen]
  have htotal : 2 * ((a : ℝ) + b) * Real.exp (-k * s) +
      2 * (2 : ℝ) ^ (a + b) * Real.exp (-c * a * b) < 1 := by
    linarith only [hdegree, hdegreeHalf, hrectangle, hrectangleHalf]
  apply ENNReal.ofReal_lt_one.mpr
  simpa only [k, c, s, neg_mul, mul_assoc] using htotal
