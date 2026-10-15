import Tablet.Preamble
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Rify

open scoped NNReal ENNReal

-- [TABLET NODE: BlowupOrderMargins]
theorem BlowupOrderMargins (η C₀ C' : ENNReal) (k : ℕ)
    (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hC₀ : 1 ≤ C₀) (hC₀top : C₀ < ⊤) (hC'top : C' < ⊤)
    (hk : 1 ≤ k) :
    ∃ C : ENNReal, 1 ≤ C ∧ C < ⊤ ∧ C₀ ≤ C ∧
      ∀ (Nbal Nred Nexec : ℕ), ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → Nbal ≤ n ∧ C / n ≤ 1 ∧
        ∀ m : ℕ, (m : ENNReal) ≤ (1 - η) * n →
          (1 - η) * n < (m : ENNReal) + 1 →
          Nred ≤ m ∧ Nexec ≤ m / k ∧ C' / (m / k : ℕ) ≤ C / n := by
-- BODY
  have hηtop : η ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hηhalf
  lift η to ℝ≥0 using hηtop
  lift C₀ to ℝ≥0 using hC₀top.ne
  lift C' to ℝ≥0 using hC'top.ne
  norm_cast at hη hC₀
  have hηhalf' : η ≤ 1 / 2 := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] using hηhalf
  have hηone : η < 1 := hηhalf'.trans_lt (by norm_num)
  let b : ℝ≥0 := 1 - η
  have hb : 0 < b := tsub_pos_iff_lt.mpr hηone
  have hkpos : (0 : ℝ≥0) < k := by exact_mod_cast (by omega : 0 < k)
  let c : ℝ≥0 := max C₀ (max 1 (4 * k * C' / b))
  have hc₀ : C₀ ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcscale : 4 * (k : ℝ≥0) * C' ≤ c * b :=
    (div_le_iff₀ hb).mp ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨c, by exact_mod_cast hc1, ENNReal.coe_lt_top, by exact_mod_cast hc₀, ?_⟩
  intro Nbal Nred Nexec
  let T : ℝ≥0 := max c (max (((Nred : ℝ≥0) + 1) / b)
    (max (2 * ((k : ℝ≥0) + 1) / b) (2 * k * (max Nexec 1 : ℕ) / b)))
  obtain ⟨N, hN⟩ := exists_nat_ge T
  refine ⟨max Nbal (max 1 N), ?_⟩
  intro n hn
  have hnBal : Nbal ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  have hTn : T ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast (by omega : N ≤ n))
  have hcn : c ≤ n := (le_max_left _ _).trans hTn
  have hnred : (Nred : ℝ≥0) + 1 ≤ b * n := by
    have h := (div_le_iff₀ hb).mp
      (((le_max_left _ _).trans (le_max_right _ _)).trans hTn)
    simpa only [mul_comm] using h
  have hnslack : 2 * ((k : ℝ≥0) + 1) ≤ b * n := by
    have h := (div_le_iff₀ hb).mp
      (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hTn)
    simpa only [mul_comm] using h
  have hnexec : 2 * (k : ℝ≥0) * (max Nexec 1 : ℕ) ≤ b * n := by
    have h := (div_le_iff₀ hb).mp
      (((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hTn)
    simpa only [mul_comm] using h
  refine ⟨hnBal, ?_, ?_⟩
  · apply (ENNReal.div_le_iff (by exact_mod_cast hnpos.ne') (by simp)).mpr
    simpa only [one_mul] using (show (c : ENNReal) ≤ n by exact_mod_cast hcn)
  intro m hmlo hmhi
  have hmlt : b * (n : ℝ≥0) < (m : ℝ≥0) + 1 := by
    exact_mod_cast hmhi
  have hmred : Nred ≤ m := by
    have : (Nred : ℝ≥0) + 1 < (m : ℝ≥0) + 1 := hnred.trans_lt hmlt
    have : (Nred : ℝ≥0) < m := (add_lt_add_iff_right _).mp this
    exact (by exact_mod_cast this : Nred < m).le
  have hmod := Nat.mod_lt m (by omega : 0 < k)
  have hdiv := Nat.mod_add_div m k
  have hmdiv : m < (m / k) * k + k := by
    rw [Nat.mul_comm (m / k) k]
    omega
  have hmdivR : (m : ℝ) < (m / k : ℕ) * (k : ℝ) + k := by exact_mod_cast hmdiv
  have hmltR := hmlt
  have hnslackR := hnslack
  have hnexecR := hnexec
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rify at hmltR hnslackR hnexecR
  have hubound : (b : ℝ) * n ≤ 2 * (m / k : ℕ) * (k : ℝ) := by
    nlinarith only [hmltR, hnslackR, hmdivR]
  have huexec : max Nexec 1 ≤ m / k := by
    have : (max Nexec 1 : ℝ) ≤ (m / k : ℕ) := by
      nlinarith only [hnexecR, hubound, hkR]
    exact_mod_cast this
  have hupos : 0 < m / k := by omega
  refine ⟨hmred, (le_max_left _ _).trans huexec, ?_⟩
  have hcscaleR := hcscale
  rify at hcscaleR
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have huR : (0 : ℝ) < (m / k : ℕ) := by exact_mod_cast hupos
  have hcR : (0 : ℝ) ≤ c := c.coe_nonneg
  have hC'R : (0 : ℝ) ≤ C' := C'.coe_nonneg
  have hratioR : (C' : ℝ) / (m / k : ℕ) ≤ (c : ℝ) / n := by
    apply (div_le_div_iff₀ huR hnR).mpr
    have hmul := mul_le_mul_of_nonneg_left hubound hcR
    have hscale := mul_le_mul_of_nonneg_right hcscaleR hnR.le
    have hnonneg : 0 ≤ (k : ℝ) * C' * n := by positivity
    nlinarith only [hmul, hscale, hnonneg, hkR]
  have hratio : C' / (m / k : ℕ) ≤ c / (n : ℝ≥0) := by exact_mod_cast hratioR
  simpa only [ENNReal.coe_div (show ((m / k : ℕ) : ℝ≥0) ≠ 0 by exact_mod_cast hupos.ne'),
    ENNReal.coe_div (show (n : ℝ≥0) ≠ 0 by exact_mod_cast hnpos.ne'), ENNReal.coe_natCast] using
      (ENNReal.coe_le_coe.mpr hratio)
