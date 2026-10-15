import Tablet.HypergeometricExponentialMoment
import Tablet.BennettEntropyLowerBound
import Tablet.NegativeExponentialQuadraticBound

-- [TABLET NODE: HypergeometricTwoTail]
theorem HypergeometricTwoTail (n s t : ℕ) (hn : 0 < n)
    (hs : s ≤ n) (ht : t ≤ n) (η : ℝ) (hη : 0 < η) :
    ∑ x ∈ (Finset.range (n + 1)).filter
      (fun x : ℕ => η * n < |(x : ℝ) - (s : ℝ) * t / n|),
      HypergeometricMass n s t x ≤
    2 * Real.exp (-(η ^ 2 / (2 * (1 + η / 3))) * n) := by
-- BODY
  classical
  let m : ℝ := (s : ℝ) * t / n
  let u : ℝ := η * n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmass (x : ℕ) : 0 ≤ HypergeometricMass n s t x := by
    unfold HypergeometricMass
    split_ifs <;> positivity
  have hmnonneg : 0 ≤ m := by dsimp [m]; positivity
  have hmle : m ≤ n := by
    dsimp [m]
    rw [div_le_iff₀ hnR]
    exact mul_le_mul (by exact_mod_cast hs) (by exact_mod_cast ht)
      (Nat.cast_nonneg t) hnR.le
  have hu : 0 < u := mul_pos hη hnR
  by_cases hmzero : m = 0
  · have hst : s = 0 ∨ t = 0 := by
      have hprod : (s : ℝ) * t = 0 := by
        have := (div_eq_zero_iff).mp hmzero
        rcases this with h | h
        · exact h
        · exact (hnR.ne' h).elim
      rcases mul_eq_zero.mp hprod with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have hsum : (∑ x ∈ (Finset.range (n + 1)).filter
        (fun x : ℕ => η * n < |(x : ℝ) - (s : ℝ) * t / n|),
        HypergeometricMass n s t x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hdev := (Finset.mem_filter.mp hx).2
      change u < |(x : ℝ) - m| at hdev
      have hxpos : 0 < x := by
        by_contra h
        have hxzero : x = 0 := Nat.eq_zero_of_not_pos h
        rw [hxzero, Nat.cast_zero, hmzero, sub_self, abs_zero] at hdev
        linarith
      rcases hst with h | h
      · subst s
        simp [HypergeometricMass, Nat.not_le.mpr hxpos]
      · subst t
        simp [HypergeometricMass, Nat.choose_eq_zero_of_lt hxpos]
    rw [hsum]
    positivity
  have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
  have hmarkov (S : Finset ℕ) (hS : S ⊆ Finset.range (n + 1))
      (l a : ℝ) (ha : ∀ x ∈ S, a ≤ l * ((x : ℝ) - m)) :
      (∑ x ∈ S, HypergeometricMass n s t x) ≤
        Real.exp (m * (Real.exp l - 1 - l) - a) := by
    have hterm (x : ℕ) (hx : x ∈ S) :
        HypergeometricMass n s t x ≤ Real.exp (-a) *
          (HypergeometricMass n s t x * Real.exp (l * ((x : ℝ) - m))) := by
      calc
        _ = HypergeometricMass n s t x * 1 := (mul_one _).symm
        _ ≤ HypergeometricMass n s t x *
            Real.exp (l * ((x : ℝ) - m) - a) := by
          apply mul_le_mul_of_nonneg_left _ (hmass x)
          simpa using Real.exp_le_exp.mpr (sub_nonneg.mpr (ha x hx))
        _ = _ := by
          rw [show l * ((x : ℝ) - m) - a = -a + l * ((x : ℝ) - m) by ring,
            Real.exp_add]
          ring
    calc
      _ ≤ ∑ x ∈ S, Real.exp (-a) *
          (HypergeometricMass n s t x * Real.exp (l * ((x : ℝ) - m))) :=
        Finset.sum_le_sum hterm
      _ = Real.exp (-a) * (∑ x ∈ S,
          HypergeometricMass n s t x * Real.exp (l * ((x : ℝ) - m))) :=
        (Finset.mul_sum ..).symm
      _ ≤ Real.exp (-a) * (∑ x ∈ Finset.range (n + 1),
          HypergeometricMass n s t x * Real.exp (l * ((x : ℝ) - m))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro x _ _
        exact mul_nonneg (hmass x) (Real.exp_nonneg _)
      _ ≤ Real.exp (-a) * Real.exp (m * (Real.exp l - 1 - l)) :=
        mul_le_mul_of_nonneg_left (HypergeometricExponentialMoment n s t hn hs ht l)
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let U := (Finset.range (n + 1)).filter (fun x : ℕ => m + u ≤ (x : ℝ))
  let L := (Finset.range (n + 1)).filter (fun x : ℕ => (x : ℝ) ≤ m - u)
  have hupper : (∑ x ∈ U, HypergeometricMass n s t x) ≤
      Real.exp (-(u ^ 2 / (2 * (m + u / 3)))) := by
    let z : ℝ := u / m
    let l : ℝ := Real.log (1 + z)
    have hz : 0 < z := div_pos hu hmpos
    have hl : 0 < l := Real.log_pos (by dsimp [z]; linarith [div_pos hu hmpos])
    have hexp : Real.exp l = 1 + z := Real.exp_log (by linarith)
    have htail := hmarkov U (Finset.filter_subset ..) l (l * u) (by
      intro x hx
      have hxU := (Finset.mem_filter.mp hx).2
      apply mul_le_mul_of_nonneg_left _ hl.le
      linarith)
    have hentropy := BennettEntropyLowerBound z hz.le
    have hscale := mul_le_mul_of_nonneg_left hentropy hmpos.le
    have huz : m * z = u := by dsimp [z]; field_simp
    have he : m * (Real.exp l - 1 - l) - l * u =
        -m * ((1 + z) * Real.log (1 + z) - z) := by
      rw [hexp, ← huz]
      dsimp [l]
      ring
    have hden : 0 < 1 + z / 3 := by positivity
    have hid : m * (z ^ 2 / (2 * (1 + z / 3))) =
        u ^ 2 / (2 * (m + u / 3)) := by
      dsimp [z]
      field_simp
    apply htail.trans
    apply Real.exp_le_exp.mpr
    rw [he]
    rw [hid] at hscale
    linarith
  have hlower : (∑ x ∈ L, HypergeometricMass n s t x) ≤
      Real.exp (-(u ^ 2 / (2 * m))) := by
    let l : ℝ := -u / m
    have hl : l < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hu) hmpos
    have htail := hmarkov L (Finset.filter_subset ..) l (-l * u) (by
      intro x hx
      have hxL := (Finset.mem_filter.mp hx).2
      have h := mul_le_mul_of_nonpos_left (show (x : ℝ) - m ≤ -u by linarith) hl.le
      nlinarith)
    apply htail.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (NegativeExponentialQuadraticBound l hl.le) hmpos.le
    have hid : m * (l ^ 2 / 2) - (-l * u) = -(u ^ 2 / (2 * m)) := by
      dsimp [l]
      field_simp
      ring
    linarith
  have hden : 0 < 2 * (1 + η / 3) := by positivity
  have hupperfinal : (∑ x ∈ U, HypergeometricMass n s t x) ≤
      Real.exp (-(η ^ 2 / (2 * (1 + η / 3))) * n) := by
    apply hupper.trans
    apply Real.exp_le_exp.mpr
    have hdenU : 0 < 2 * (m + u / 3) := by positivity
    have hcompare : 2 * (m + u / 3) ≤ 2 * (n : ℝ) * (1 + η / 3) := by
      dsimp [u]
      nlinarith
    have h := div_le_div_of_nonneg_left (sq_nonneg u) hdenU hcompare
    have hid : u ^ 2 / (2 * (n : ℝ) * (1 + η / 3)) =
        (η ^ 2 / (2 * (1 + η / 3))) * n := by
      dsimp [u]
      field_simp
    rw [hid] at h
    linarith
  have hlowerfinal : (∑ x ∈ L, HypergeometricMass n s t x) ≤
      Real.exp (-(η ^ 2 / (2 * (1 + η / 3))) * n) := by
    apply hlower.trans
    apply Real.exp_le_exp.mpr
    have hcompare : 2 * m ≤ 2 * (n : ℝ) * (1 + η / 3) := by
      nlinarith [mul_nonneg hnR.le hη.le]
    have h := div_le_div_of_nonneg_left (sq_nonneg u) (by positivity : 0 < 2 * m) hcompare
    have hid : u ^ 2 / (2 * (n : ℝ) * (1 + η / 3)) =
        (η ^ 2 / (2 * (1 + η / 3))) * n := by
      dsimp [u]
      field_simp
    rw [hid] at h
    linarith
  have hevent : (Finset.range (n + 1)).filter
      (fun x : ℕ => η * n < |(x : ℝ) - (s : ℝ) * t / n|) ⊆ U ∪ L := by
    intro x hx
    obtain ⟨hxr, hxdev⟩ := Finset.mem_filter.mp hx
    change u < |(x : ℝ) - m| at hxdev
    rcases lt_abs.mp hxdev with h | h
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨hxr, by linarith⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨hxr, by linarith⟩
  calc
    _ ≤ ∑ x ∈ U ∪ L, HypergeometricMass n s t x :=
      Finset.sum_le_sum_of_subset_of_nonneg hevent (fun x _ _ => hmass x)
    _ ≤ (∑ x ∈ U, HypergeometricMass n s t x) +
        (∑ x ∈ L, HypergeometricMass n s t x) := by
      rw [← Finset.sum_union_inter]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun x _ => hmass x))
    _ ≤ _ := by linarith
