import Tablet.Preamble
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- [TABLET NODE: BalancedDegreeVarianceBound]
theorem BalancedDegreeVarianceBound {A : Type*} (U : Finset A) (d : A → ℝ)
    (q δ p : ℝ) (hq : 0 ≤ q) (hqn : q ≤ U.card)
    (hδ : 0 ≤ δ) (hδp : δ ≤ p) (hp : p ≤ 1)
    (hfirst : (q - 5 * δ * U.card) * (p - δ) * U.card ≤ ∑ u ∈ U, d u)
    (hsecond : (∑ u ∈ U, (d u) ^ 2) ≤
      (U.card : ℝ) * q ^ 2 * (p + δ) ^ 2 + 5 * δ * (U.card : ℝ) ^ 3) :
    (∑ u ∈ U, (d u - p * q) ^ 2) ≤ 20 * δ * (U.card : ℝ) ^ 3 := by
-- BODY
  have hn : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have hp0 : 0 ≤ p := hδ.trans hδp
  have hδ1 : δ ≤ 1 := hδp.trans hp
  have hcenterId : (∑ u ∈ U, (d u - p * q) ^ 2) =
      (∑ u ∈ U, (d u) ^ 2) - 2 * p * q * (∑ u ∈ U, d u) +
        (U.card : ℝ) * p ^ 2 * q ^ 2 := by
    calc
      _ = ∑ u ∈ U, ((d u) ^ 2 - 2 * p * q * d u + (p * q) ^ 2) := by
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hscale := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ 2 * p * q by positivity)
  have hcenter : (∑ u ∈ U, (d u - p * q) ^ 2) ≤
      (U.card : ℝ) * q ^ 2 * (4 * p * δ + δ ^ 2) +
        10 * δ * (U.card : ℝ) ^ 2 * q * (p * (p - δ)) +
        5 * δ * (U.card : ℝ) ^ 3 := by
    rw [hcenterId]
    calc
      _ ≤ ((U.card : ℝ) * q ^ 2 * (p + δ) ^ 2 + 5 * δ * (U.card : ℝ) ^ 3) -
          2 * p * q * ((q - 5 * δ * U.card) * (p - δ) * U.card) +
          (U.card : ℝ) * p ^ 2 * q ^ 2 := by linarith only [hsecond, hscale]
      _ = _ := by ring
  have hcoeff : 4 * p * δ + δ ^ 2 ≤ 5 * δ := by
    nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hp),
      mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hcoeff' : p * (p - δ) ≤ 1 := by
    nlinarith only [hp, mul_nonneg hp0 (sub_nonneg.mpr hp), mul_nonneg hp0 hδ]
  have hqsq : q ^ 2 ≤ (U.card : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hqn) (add_nonneg hn hq)]
  have hterm0 : (U.card : ℝ) * q ^ 2 * (4 * p * δ + δ ^ 2) ≤
      5 * δ * (U.card : ℝ) ^ 3 := by
    calc
      _ ≤ (U.card : ℝ) * q ^ 2 * (5 * δ) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = (5 * δ * U.card) * q ^ 2 := by ring
      _ ≤ (5 * δ * U.card) * (U.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hqsq (by positivity)
      _ = _ := by ring
  have hterm1 : 10 * δ * (U.card : ℝ) ^ 2 * q * (p * (p - δ)) ≤
      10 * δ * (U.card : ℝ) ^ 3 := by
    calc
      _ ≤ 10 * δ * (U.card : ℝ) ^ 2 * q * 1 :=
        mul_le_mul_of_nonneg_left hcoeff' (by positivity)
      _ = (10 * δ * (U.card : ℝ) ^ 2) * q := by ring
      _ ≤ (10 * δ * (U.card : ℝ) ^ 2) * U.card :=
        mul_le_mul_of_nonneg_left hqn (by positivity)
      _ = _ := by ring
  linarith only [hcenter, hterm0, hterm1]
