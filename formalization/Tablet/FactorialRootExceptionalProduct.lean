import Tablet.Preamble
import Tablet.FactorialRootMonotone
import Tablet.LogFactorialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

open Filter
open scoped BigOperators Topology

-- [TABLET NODE: FactorialRootExceptionalProduct]
theorem FactorialRootExceptionalProduct (D θ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hc : D + 3 * θ < 1) :
    ∃ y₀ : ℕ, 0 < y₀ ∧ ∀ (y : ℕ), y₀ ≤ y →
      ∀ (r : Fin y → ℕ), (∀ i, 0 < r i) → (∀ i, r i ≤ y) →
        ((((Finset.univ : Finset (Fin y)).filter fun i =>
          (D + θ) * (y : ℝ) < (r i : ℝ)).card : ℝ) ≤ θ * (y : ℝ)) →
        (∏ i : Fin y, Real.rpow (Nat.factorial (r i) : ℝ) ((r i : ℝ)⁻¹)) ≤
          (D + 3 * θ) ^ y * (y.factorial : ℝ) := by
-- BODY
  classical
  let a : ℕ → ℝ := fun n => Real.rpow (n.factorial : ℝ) (n : ℝ)⁻¹
  have apos (n : ℕ) : 0 < a n := Real.rpow_pos_of_pos (by positivity) _
  have ratio (m y : ℕ) (hm : 0 < m) (hmy : m ≤ y) :
      a m / a y ≤ (m : ℝ) / y * Real.exp ((Real.log y + 1) / m) := by
    have hy : 0 < y := hm.trans_le hmy
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hyR : 0 < (y : ℝ) := by exact_mod_cast hy
    have hlogs : Real.log m ≤ Real.log y := Real.log_le_log hmR (by exact_mod_cast hmy)
    have hu : Real.log (m.factorial : ℝ) / m ≤
        Real.log m - 1 + (Real.log y + 1) / m := by
      apply (div_le_iff₀ hmR).2
      have hb := (LogFactorialBounds m hm).2
      have hid : (Real.log m - 1 + (Real.log y + 1) / m) * m =
          (m : ℝ) * Real.log m - m + Real.log y + 1 := by field_simp; ring
      rw [hid]
      linarith
    have hl : Real.log y - 1 ≤ Real.log (y.factorial : ℝ) / y := by
      apply (le_div_iff₀ hyR).2
      nlinarith [(LogFactorialBounds y hy).1]
    have hlog : Real.log (m.factorial : ℝ) / m - Real.log (y.factorial : ℝ) / y ≤
        Real.log ((m : ℝ) / y) + (Real.log y + 1) / m := by
      rw [Real.log_div hmR.ne' hyR.ne']
      linarith
    dsimp [a]
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
      ← Real.exp_sub]
    simp only [← div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Real.log ((m : ℝ) / y) + (Real.log y + 1) / m) :=
        Real.exp_le_exp.mpr hlog
      _ = _ := by rw [Real.exp_add, Real.exp_log (div_pos hmR hyR)]
  let x := D + 2 * θ
  let γ := Real.log ((x + θ) / x) - θ * Real.log (1 / x)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxθ : 0 < x + θ := by positivity
  have hx1 : x < 1 := by dsimp [x]; linarith
  have hlogx : Real.log x < 0 := Real.log_neg hx hx1
  have hγ : 0 < γ := by
    have hl : 0 < Real.log (1 / x) := Real.log_pos ((one_lt_div hx).2 hx1)
    have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hmax : x * Real.log (1 / x) ≤ 1 / Real.exp 1 := by
      have ht := Real.log_le_sub_one_of_pos (div_pos (one_div_pos.mpr hx) (Real.exp_pos 1))
      rw [Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp] at ht
      have ht' := mul_le_mul_of_nonneg_left ht hx.le
      have hid : x * (1 / x / Real.exp 1 - 1) = 1 / Real.exp 1 - x := by field_simp
      rw [hid] at ht'
      nlinarith
    have hhalf : x * Real.log (1 / x) ≤ 1 / 2 :=
      hmax.trans (one_div_le_one_div_of_le (by norm_num) he)
    have hsmall : (x + θ) * Real.log (1 / x) < 1 := by
      have hθx : θ < x / 2 := by dsimp [x]; linarith
      nlinarith [mul_lt_mul_of_pos_right hθx hl]
    have hstrict := Real.log_lt_sub_one_of_pos (div_pos hx hxθ)
      (show x / (x + θ) ≠ 1 by
        intro h; have := (div_eq_one_iff_eq hxθ.ne').1 h; linarith)
    rw [Real.log_div hx.ne' hxθ.ne'] at hstrict
    have hstrict' : θ / (x + θ) < Real.log ((x + θ) / x) := by
      rw [Real.log_div hxθ.ne' hx.ne']
      have hid : x / (x + θ) - 1 = -(θ / (x + θ)) := by field_simp; ring
      rw [hid] at hstrict
      linarith
    have habs : θ * Real.log (1 / x) < θ / (x + θ) := by
      apply (lt_div_iff₀ hxθ).2
      nlinarith [mul_lt_mul_of_pos_left hsmall hθ]
    dsimp [γ]
    linarith
  have threshold : ∃ y₀ : ℕ, 0 < y₀ ∧ ∀ y : ℕ, y₀ ≤ y →
      1 / (y : ℝ) ≤ θ ∧ (Real.log y + 1) / (θ * y) ≤ γ / 2 := by
    have hcast : Tendsto (fun y : ℕ => (y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun y : ℕ => 1 / (y : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hcast
    have hlog : Tendsto (fun y : ℕ => Real.log y / (θ * y)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_log_div_mul_add_atTop θ 0 1 hθ.ne').comp hcast
    have hone : Tendsto (fun y : ℕ => 1 / (θ * y)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hcast.const_mul_atTop hθ)
    have hdelta : Tendsto (fun y : ℕ => (Real.log y + 1) / (θ * y)) atTop (𝓝 0) := by
      simpa only [zero_add, ← add_div] using hlog.add hone
    have he : ∀ᶠ y : ℕ in atTop,
        1 ≤ y ∧ 1 / (y : ℝ) < θ ∧ (Real.log y + 1) / (θ * y) < γ / 2 := by
      filter_upwards [eventually_ge_atTop 1, hinv.eventually_lt_const hθ,
        hdelta.eventually_lt_const (show 0 < γ / 2 by positivity)] with y hy hi hd
      exact ⟨hy, hi, hd⟩
    obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 he
    exact ⟨y₀, (hy₀ y₀ le_rfl).1, fun y hy =>
      ⟨(hy₀ y hy).2.1.le, (hy₀ y hy).2.2.le⟩⟩
  obtain ⟨y₀, hy₀, hthreshold⟩ := threshold
  refine ⟨y₀, hy₀, ?_⟩
  intro y hyy₀ r hr hry hbad
  have hy : 0 < y := hy₀.trans_le hyy₀
  have hyR : 0 < (y : ℝ) := by exact_mod_cast hy
  have hy1 : 1 ≤ (y : ℝ) := by exact_mod_cast hy
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  obtain ⟨hinv, hδγ⟩ := hthreshold y hyy₀
  let δ := (Real.log y + 1) / (θ * y)
  have hδ : 0 ≤ δ := div_nonneg (by linarith) (by positivity)
  have hθy : 1 ≤ θ * y := (div_le_iff₀ hyR).1 hinv
  have controlled (m : ℕ) (hm : 0 < m) (hmy : m ≤ y)
      (hlow : θ * y ≤ (m : ℝ)) (hupp : (m : ℝ) / y ≤ x) :
      a m / a y ≤ x * Real.exp δ := by
    apply (ratio m y hm hmy).trans
    apply mul_le_mul hupp _ (Real.exp_pos _).le hx.le
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hlow
  have hordinary (i : Fin y) (hi : ¬ (D + θ) * (y : ℝ) < (r i : ℝ)) :
      a (r i) / a y ≤ x * Real.exp δ := by
    by_cases hlarge : θ * y ≤ (r i : ℝ)
    · apply controlled (r i) (hr i) (hry i) hlarge
      apply (div_le_iff₀ hyR).2
      have : (r i : ℝ) ≤ (D + θ) * y := le_of_not_gt hi
      dsimp [x]
      nlinarith [mul_nonneg hθ.le hyR.le]
    · let s := Nat.ceil (θ * (y : ℝ))
      have hs : 0 < s := Nat.ceil_pos.mpr (by positivity)
      have hslow : θ * y ≤ (s : ℝ) := Nat.le_ceil _
      have hsup : (s : ℝ) < θ * y + 1 := Nat.ceil_lt_add_one (by positivity)
      have hsyR : (s : ℝ) ≤ (y : ℝ) := by
        have : 2 * θ < 1 := by linarith
        nlinarith [mul_lt_mul_of_pos_right this hyR]
      have hsy : s ≤ y := by exact_mod_cast hsyR
      have hrs : r i ≤ s := by
        have : (r i : ℝ) ≤ (s : ℝ) := (not_le.mp hlarge).le.trans hslow
        exact_mod_cast this
      have hsupx : (s : ℝ) / y ≤ x := by
        apply (div_le_iff₀ hyR).2
        dsimp [x]
        nlinarith [mul_nonneg hD.le hyR.le]
      exact (div_le_div_of_nonneg_right (FactorialRootMonotone (r i) s (hr i) hrs)
        (apos y).le).trans (controlled s hs hsy hslow hsupx)
  let bad : Finset (Fin y) := Finset.univ.filter fun i => (D + θ) * (y : ℝ) < (r i : ℝ)
  let t : Fin y → ℝ := fun i => if i ∈ bad then 0 else Real.log x + δ
  have hrow (i : Fin y) : a (r i) ≤ a y * Real.exp (t i) := by
    by_cases hi : i ∈ bad
    · simp only [t, if_pos hi, Real.exp_zero, mul_one]
      exact FactorialRootMonotone (r i) y (hr i) (hry i)
    · have hni : ¬ (D + θ) * (y : ℝ) < (r i : ℝ) := by simpa [bad] using hi
      have hh := (div_le_iff₀ (apos y)).1 (hordinary i hni)
      simpa [t, hi, Real.exp_add, Real.exp_log hx, mul_comm, mul_left_comm, mul_assoc] using hh
  have hsum : ∑ i, t i = ((y : ℝ) - bad.card) * (Real.log x + δ) := by
    have ht (i : Fin y) : t i = (Real.log x + δ) -
        (if i ∈ bad then Real.log x + δ else 0) := by
      dsimp [t]; split_ifs <;> ring
    simp_rw [ht]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_mem, sub_mul]
    ring
  have hk : (bad.card : ℝ) ≤ θ * y := hbad
  have hk0 : 0 ≤ (bad.card : ℝ) := Nat.cast_nonneg _
  have hexponent : ((y : ℝ) - bad.card) * (Real.log x + δ) ≤
      (y : ℝ) * Real.log (x + θ) := by
    have hsign := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) hlogx.le
    have hδsign := mul_nonneg hk0 hδ
    have habs : (1 - θ) * Real.log x + δ ≤ Real.log (x + θ) := by
      have hδγ' : δ ≤ γ := hδγ.trans (by linarith)
      dsimp [γ] at hδγ'
      rw [Real.log_div hxθ.ne' hx.ne', Real.log_div one_ne_zero hx.ne', Real.log_one] at hδγ'
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left habs hyR.le]
  have hprod : (∏ i : Fin y, a (r i)) ≤ a y ^ y * Real.exp (∑ i, t i) := by
    calc
      _ ≤ ∏ i : Fin y, (a y * Real.exp (t i)) :=
        Finset.prod_le_prod (fun i _ => (apos (r i)).le) (fun i _ => hrow i)
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.exp_sum]; simp
  have hpow : a y ^ y = (y.factorial : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) hy.ne'
  have hfinal : Real.exp (∑ i, t i) ≤ (D + 3 * θ) ^ y := by
    rw [hsum]
    have hh := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_nat_mul, Real.exp_log hxθ] at hh
    have hxid : x + θ = D + 3 * θ := by dsimp [x]; ring
    simpa only [hxid] using hh
  change (∏ i : Fin y, a (r i)) ≤ _
  rw [hpow] at hprod
  exact hprod.trans (by simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hfinal (Nat.cast_nonneg y.factorial))
