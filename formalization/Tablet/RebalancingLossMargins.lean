import Tablet.Preamble
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Rify

open scoped NNReal ENNReal

-- [TABLET NODE: RebalancingLossMargins]
theorem RebalancingLossMargins (Δ : ℕ) (d d' a : ENNReal)
    (hΔ : 1 ≤ Δ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hd' : 0 < d') (hd'd : d' ≤ d / 4) (ha : 0 < a) (haquarter : a ≤ 1 / 4) :
    ∃ ε₀' : ENNReal, 0 < ε₀' ∧ ε₀' ≤ min (1 / 4) (d' / 2) ∧
    ∀ ε' : ENNReal, 0 < ε' → ε' ≤ ε₀' →
      ∃ ε₀ : ENNReal, 0 < ε₀ ∧
      ∀ ε : ENNReal, 0 < ε → ε ≤ ε₀ →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ m k : ℕ,
          4 ≤ n ∧ ε ≤ a ∧ ε ≤ 1 / 4 ∧ ε ≤ d / 4 ∧ ε' < ⊤ ∧
          (m : ENNReal) ≤ (1 - ε) * n ∧
          (1 - ε) * n < (m : ENNReal) + 1 ∧
          (n : ENNReal) / 2 ≤ m ∧ m ≤ n ∧
          (k : ENNReal) ≤ 4 * ε * n ∧
          (d' - ε') + (8 * Δ * Δ * ε) / ε' ≤ d - ε ∧
          ∀ N : ℕ, (1 - ε) * n ≤ N → (N : ENNReal) ≤ (1 + ε) * n →
            m ≤ N ∧ N - m ≤ k ∧ ((N - m : ℕ) : ENNReal) ≤ 3 * ε * n ∧
            (3 + 4 * Δ * Δ) * ε * n ≤ a * N ∧
            (d / 2) * n ≤ (d - ε) * N ∧
            ε * N ≤ ε' * m ∧
            (d' - ε') * m ≤ (d - ε) * N - 3 * ε * n ∧
            (d' - ε') * m ≤ (d - ε) * N - 3 * ε * n - 4 * Δ * Δ * ε * n := by
-- BODY
  -- Finite representatives preserve all the extended-real operations used below.
  have hdt : d ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hd1
  have hd't : d' ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.div_ne_top hdt (by norm_num)) hd'd
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) haquarter
  lift d to ℝ≥0 using hdt
  lift d' to ℝ≥0 using hd't
  lift a to ℝ≥0 using hat
  norm_cast at hd hd1 hd' ha
  have hdd : d' ≤ d / 4 := by exact_mod_cast hd'd
  let e₀' : ℝ≥0 := min (1 / 4) (d' / 2)
  have he₀' : 0 < e₀' := by dsimp [e₀']; positivity
  refine ⟨e₀', by exact_mod_cast he₀', ?_, ?_⟩
  · simp [e₀', ENNReal.coe_min, ENNReal.coe_div]
  intro ε' hε' hε'₀
  have hε't : ε' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hε'₀
  lift ε' to ℝ≥0 using hε't
  norm_cast at hε' hε'₀
  let K : ℝ≥0 := 3 + 4 * Δ * Δ
  have hK : 0 < K := by dsimp [K]; positivity
  have hΔpos : (0 : ℝ≥0) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  let e₀ : ℝ≥0 := min (1 / 4) (min (d / 4) (min a
    (min (a / (2 * K)) (min (ε' / 4) (min (d / (4 * K))
      (d * ε' / (32 * Δ * Δ)))))))
  have he₀ : 0 < e₀ := by dsimp [e₀]; positivity
  refine ⟨e₀, by exact_mod_cast he₀, ?_⟩
  intro ε hε hε₀
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hε₀
  lift ε to ℝ≥0 using hεt
  norm_cast at hε hε₀
  have hb := hε₀
  simp only [e₀, le_min_iff] at hb
  rcases hb with ⟨hequarter, hedquarter, hea, heaK, hee', hedK, hedensity⟩
  have heone : ε ≤ 1 :=
    le_trans hequarter (div_le_self zero_le_one (by norm_num))
  have hed : ε ≤ d := le_trans hedquarter (by exact div_le_self (zero_le d) (by norm_num))
  have he'd : ε' ≤ d' := hε'₀.trans
    ((min_le_right _ _).trans (div_le_self (zero_le d') (by norm_num)))
  refine ⟨max 4 ⌈(1 / ε : ℝ≥0)⌉₊, ?_⟩
  intro n hn
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hinv : (1 / ε : ℝ≥0) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hn))
  have hen : (1 : ℝ≥0) ≤ ε * n := by
    have := (div_le_iff₀ hε).mp hinv
    simpa [mul_comm] using this
  let m := ⌊(1 - ε) * (n : ℝ≥0)⌋₊
  let k := ⌈3 * ε * (n : ℝ≥0)⌉₊
  refine ⟨m, k, ?_⟩
  refine ⟨hn4, by exact_mod_cast hea, ?_, by exact_mod_cast hedquarter,
    ENNReal.coe_lt_top, ?_⟩
  · simpa [ENNReal.coe_div] using (ENNReal.coe_le_coe.mpr hequarter)
  norm_cast
  simp only [← ENNReal.coe_div hε'.ne']
  norm_cast
  have hmle : (m : ℝ≥0) ≤ (1 - ε) * n := Nat.floor_le (zero_le _)
  have hmlt : (1 - ε) * (n : ℝ≥0) < (m : ℝ≥0) + 1 := Nat.lt_floor_add_one _
  have hkle : (k : ℝ≥0) < 3 * ε * n + 1 := Nat.ceil_lt_add_one (zero_le _)
  have hkge : 3 * ε * (n : ℝ≥0) ≤ k := Nat.le_ceil _
  have hmR := hmle
  have hmR' := hmlt
  have hkR := hkle
  rify [heone] at hmR hmR'
  rify at hkR
  rify at hd hd1 hd' hdd ha hε' hε hequarter hedquarter heaK hee' hedK hedensity hen hK hΔpos
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have henquarter : (ε : ℝ) * n ≤ (n : ℝ) / 4 := by
    nlinarith only [mul_le_mul_of_nonneg_right hequarter hnnonneg]
  have hmhalf : (n : ℝ≥0) / 2 ≤ m := by
    rify
    nlinarith only [hmR', hnR, henquarter]
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by
      nlinarith only [hmR, mul_nonneg hε.le hnnonneg]
    exact_mod_cast this
  have hkupper : (k : ℝ≥0) ≤ 4 * ε * n := by rify; linarith only [hkR, hen]
  have haK : (K : ℝ) * ε ≤ (a : ℝ) / 2 := by
    have := (le_div_iff₀ (show (0 : ℝ) < 2 * K by positivity)).mp heaK
    nlinarith only [this]
  have hdK : (K : ℝ) * ε ≤ (d : ℝ) / 4 := by
    have := (le_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hedK
    nlinarith only [this]
  have hdensity : (8 * (Δ : ℝ) * Δ * ε) / ε' ≤ (d : ℝ) / 4 := by
    apply (div_le_iff₀ hε').mpr
    have := (le_div_iff₀ (show (0 : ℝ) < 32 * Δ * Δ by positivity)).mp hedensity
    nlinarith only [this]
  have hdens : d' - ε' + (8 * Δ * Δ * ε : ℝ≥0) / ε' ≤ d - ε := by
    rify [he'd, hed]
    linarith only [hdd, hdensity, hedquarter, hd.le, hε'.le]
  refine ⟨hmle, ?_, ?_, hmn, hkupper, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using hmlt
  · simpa [ENNReal.coe_div] using (ENNReal.coe_le_coe.mpr hmhalf)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdens
  intro N hNlo hNhi
  have hmN : m ≤ N := by
    exact_mod_cast hmle.trans hNlo
  have hNloR := hNlo
  have hNhiR := hNhi
  rify [heone] at hNloR hNhiR
  have hNhalf : (n : ℝ) / 2 ≤ N := by nlinarith only [hNloR, henquarter, hnnonneg]
  have hNtwo : (N : ℝ) ≤ 2 * n := by nlinarith only [hNhiR, henquarter, hnnonneg]
  have hloss : ((N - m : ℕ) : ℝ≥0) ≤ 3 * ε * n := by
    -- Order the natural operands before transporting their difference.
    have hmNnn : (m : ℝ≥0) ≤ N := by exact_mod_cast hmN
    rify [hmNnn]
    nlinarith only [hmR', hNhiR, hen]
  have hlossk : N - m ≤ k := by exact_mod_cast hloss.trans hkge
  have hsmall : K * ε * (n : ℝ≥0) ≤ a * N := by
    rify
    nlinarith only [mul_le_mul_of_nonneg_right haK hnnonneg,
      mul_le_mul_of_nonneg_left hNhalf ha.le]
  have hdegbase : (d : ℝ) / 2 ≤ ((d : ℝ) - ε) * (1 - (ε : ℝ)) := by
    nlinarith only [hedquarter, mul_nonneg (show (0 : ℝ) ≤ ε by positivity)
      (show (0 : ℝ) ≤ ε by positivity),
      mul_le_mul_of_nonneg_right hd1 (show (0 : ℝ) ≤ ε by positivity)]
  have hdegree : (d / 2 : ℝ≥0) * n ≤ (d - ε) * N := by
    rify [hed]
    have hde : (0 : ℝ) ≤ (d : ℝ) - ε := sub_nonneg.mpr (by exact_mod_cast hed)
    nlinarith only [mul_le_mul_of_nonneg_right hdegbase hnnonneg,
      mul_le_mul_of_nonneg_left hNloR hde]
  have htransfer : ε * (N : ℝ≥0) ≤ ε' * m := by
    have hmhalfR := hmhalf
    rify at hmhalfR ⊢
    nlinarith only [mul_le_mul_of_nonneg_left hNtwo hε.le,
      mul_le_mul_of_nonneg_right hee' hnnonneg,
      mul_le_mul_of_nonneg_left hmhalfR hε'.le]
  have hstrongadd : (d' - ε') * (m : ℝ≥0) +
      4 * Δ * Δ * ε * n + 3 * ε * n ≤ (d - ε) * N := by
    have hdegreeR := hdegree
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    rify [he'd, hed] at hdegreeR ⊢
    have hbound : ((d' : ℝ) - ε') * m ≤ (d : ℝ) / 4 * n := by
      have : (d' : ℝ) - ε' ≤ (d : ℝ) / 4 := by linarith only [hdd, hε'.le]
      have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith only [mul_le_mul_of_nonneg_right this hmnonneg,
        mul_le_mul_of_nonneg_left hmnR (show (0 : ℝ) ≤ (d : ℝ) / 4 by positivity)]
    have hKn := mul_le_mul_of_nonneg_right hdK hnnonneg
    dsimp [K] at hKn
    push_cast at hKn
    nlinarith only [hbound, hKn, hdegreeR]
  have hstrong : (d' - ε') * (m : ℝ≥0) ≤
      (d - ε) * N - 3 * ε * n - 4 * Δ * Δ * ε * n := by
    -- The additive bound justifies both truncated subtractions.
    apply le_tsub_of_add_le_right
    apply le_tsub_of_add_le_right
    exact hstrongadd
  have hweak : (d' - ε') * (m : ℝ≥0) ≤ (d - ε) * N - 3 * ε * n :=
    hstrong.trans (tsub_le_self)
  refine ⟨hmN, hlossk, hloss, ?_, hdegree, htransfer, hweak, ?_⟩
  · simpa only [K, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hsmall
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hstrong
