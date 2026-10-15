import Tablet.Preamble
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- [TABLET NODE: RestrictedDegreeVarianceBound]
theorem RestrictedDegreeVarianceBound {A : Type*} (U : Finset A) (d : A → ℝ)
    (q k δ p η : ℝ) (hq : 0 < q) (hk : 0 ≤ k)
    (hδ : 0 ≤ δ) (hδp : δ ≤ p) (hp : p ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlarge : η * k < q)
    (hfirst : (q - 6 * δ * k) * (p - δ) * U.card ≤ ∑ u ∈ U, d u)
    (hsecond : (∑ u ∈ U, (d u) ^ 2) ≤
      (U.card : ℝ) * q ^ 2 * (p + δ) ^ 2 + 6 * δ * k ^ 2 * U.card) :
    η ^ 2 * (∑ u ∈ U, (d u - p * q) ^ 2) ≤ 23 * δ * U.card * q ^ 2 := by
-- BODY
  let t : ℝ := k / q
  have ht : 0 ≤ t := div_nonneg hk hq.le
  have htq : t * q = k := div_mul_cancel₀ _ hq.ne'
  have htratio : t < 1 / η := by
    exact (div_lt_div_iff₀ hq hη).mpr (by simpa only [mul_comm, mul_one] using hlarge)
  have hpt : 0 ≤ p := hδ.trans hδp
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
  have hcenter : (∑ u ∈ U, (d u - p * q) ^ 2) ≤
      (U.card : ℝ) * q ^ 2 *
        (4 * p * δ + δ ^ 2 + 12 * p * δ * (p - δ) * t + 6 * δ * t ^ 2) := by
    have hscale := mul_le_mul_of_nonneg_left hfirst
      (show 0 ≤ 2 * p * q by positivity)
    calc
      _ = _ := hcenterId
      _ ≤ ((U.card : ℝ) * q ^ 2 * (p + δ) ^ 2 + 6 * δ * k ^ 2 * U.card) -
          2 * p * q * ((q - 6 * δ * k) * (p - δ) * U.card) +
          (U.card : ℝ) * p ^ 2 * q ^ 2 := by linarith only [hsecond, hscale]
      _ = _ := by rw [← htq]; ring
  have hδ1 : δ ≤ 1 := hδp.trans hp
  have hsmall0 : 4 * p * δ + δ ^ 2 ≤ 5 * δ := by
    nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hp), mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hsmall1 : p * (p - δ) ≤ 1 := by
    nlinarith only [hp, mul_nonneg hpt (sub_nonneg.mpr hp), mul_nonneg hpt hδ]
  have hsmall2 : 12 * p * δ * (p - δ) * t ≤ 12 * δ * t := by
    have := mul_le_mul_of_nonneg_left hsmall1 (show 0 ≤ 12 * δ * t by positivity)
    convert this using 1 <;> ring
  have hcoefficient : 4 * p * δ + δ ^ 2 + 12 * p * δ * (p - δ) * t + 6 * δ * t ^ 2 ≤
      δ * (5 + 12 * t + 6 * t ^ 2) := by linarith only [hsmall0, hsmall2]
  have hcenter' : (∑ u ∈ U, (d u - p * q) ^ 2) ≤
      δ * (U.card : ℝ) * q ^ 2 * (5 + 12 * t + 6 * t ^ 2) := by
    calc
      _ ≤ _ := hcenter
      _ ≤ (U.card : ℝ) * q ^ 2 * (δ * (5 + 12 * t + 6 * t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoefficient (by positivity)
      _ = _ := by ring
  have hηt : η * t ≤ 1 := by
    have := (lt_div_iff₀ hη).mp htratio
    simpa only [mul_comm] using this.le
  have hηsq : η ^ 2 ≤ 1 := by
    nlinarith only [hη1, mul_nonneg hη.le (sub_nonneg.mpr hη1)]
  have hηsqt : η ^ 2 * t ≤ 1 := by
    nlinarith only [hηt, mul_nonneg (sub_nonneg.mpr hη1) (mul_nonneg hη.le ht)]
  have hηsqt2 : η ^ 2 * t ^ 2 ≤ 1 := by
    nlinarith only [hηt, mul_nonneg (mul_nonneg hη.le ht) (sub_nonneg.mpr hηt)]
  have hpoly : η ^ 2 * (5 + 12 * t + 6 * t ^ 2) ≤ 23 := by
    nlinarith only [hηsq, hηsqt, hηsqt2]
  calc
    _ ≤ η ^ 2 * (δ * (U.card : ℝ) * q ^ 2 * (5 + 12 * t + 6 * t ^ 2)) :=
      mul_le_mul_of_nonneg_left hcenter' (sq_nonneg _)
    _ = (δ * (U.card : ℝ) * q ^ 2) * (η ^ 2 * (5 + 12 * t + 6 * t ^ 2)) := by ring
    _ ≤ (δ * (U.card : ℝ) * q ^ 2) * 23 := mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by ring
