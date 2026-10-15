import Tablet.HypergeometricMass
import Tablet.ElementarySymmetricMean
import Tablet.WeightedSubsetIntersectionSum

-- [TABLET NODE: HypergeometricExponentialMoment]
theorem HypergeometricExponentialMoment (n s t : ℕ)
    (hn : 0 < n) (hs : s ≤ n) (ht : t ≤ n) (l : ℝ) :
    ∑ x ∈ Finset.range (n + 1), HypergeometricMass n s t x *
      Real.exp (l * ((x : ℝ) - (s : ℝ) * t / n)) ≤
    Real.exp (((s : ℝ) * t / n) * (Real.exp l - 1 - l)) := by
-- BODY
  classical
  obtain ⟨M, _hMsub, hM⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ : Finset (Fin n)).card by simpa using ht)
  let a : Fin n → ℝ := fun i => if i ∈ M then Real.exp l else 1
  let m : ℝ := (s : ℝ) * t / n
  let z : ℝ := (t : ℝ) / n * (Real.exp l - 1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (n.choose s : ℝ) := by exact_mod_cast Nat.choose_pos hs
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    split_ifs <;> positivity
  have hraw := WeightedSubsetIntersectionSum n s hs M (Real.exp l)
  rw [hM] at hraw
  have hid :
      (∑ x ∈ Finset.range (n + 1),
        HypergeometricMass n s t x * Real.exp (l * (x : ℝ))) =
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        ∏ i ∈ A, a i) / (n.choose s : ℝ) := by
    rw [show (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      ∏ i ∈ A, a i) = _ from hraw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxs : x ≤ s
    · simp only [HypergeometricMass, if_pos hxs]
      rw [show l * (x : ℝ) = (x : ℝ) * l by ring, Real.exp_nat_mul]
      field_simp [hc.ne']
    · simp [HypergeometricMass, hxs]
  have hsum : (∑ i, a i) = (n : ℝ) + (t : ℝ) * (Real.exp l - 1) := by
    have hf : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ M) = M := by
      ext i
      simp
    have hg : (Finset.univ : Finset (Fin n)).filter (fun i => i ∉ M) =
        Finset.univ \ M := by
      ext i
      simp
    have hcard : (Finset.univ \ M).card = n - t := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ M)]
      simp [hM]
    dsimp [a]
    rw [Finset.sum_ite, hf, hg]
    simp only [Finset.sum_const, nsmul_eq_mul, hM, hcard, mul_one]
    rw [Nat.cast_sub ht]
    ring
  have hmean : (∑ i, a i) / (n : ℝ) = 1 + z := by
    rw [hsum]
    dsimp [z]
    field_simp [hnR.ne']
  have hbase : 0 ≤ 1 + z := by
    rw [← hmean]
    exact div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) hnR.le
  have hbound :
      (∑ x ∈ Finset.range (n + 1),
        HypergeometricMass n s t x * Real.exp (l * (x : ℝ))) ≤
      Real.exp ((s : ℝ) * z) := by
    calc
      _ ≤ (1 + z) ^ s := by
        rw [hid, ← hmean]
        exact ElementarySymmetricMean n s hn hs a ha
      _ ≤ (Real.exp z) ^ s :=
        pow_le_pow_left₀ hbase (by simpa [add_comm] using Real.add_one_le_exp z) s
      _ = _ := (Real.exp_nat_mul z s).symm
  have hcenter :
      (∑ x ∈ Finset.range (n + 1),
        HypergeometricMass n s t x * Real.exp (l * ((x : ℝ) - m))) =
      Real.exp (-l * m) *
        (∑ x ∈ Finset.range (n + 1),
          HypergeometricMass n s t x * Real.exp (l * (x : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have he : Real.exp (l * ((x : ℝ) - m)) =
        Real.exp (-l * m) * Real.exp (l * (x : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  calc
    _ = Real.exp (-l * m) *
        (∑ x ∈ Finset.range (n + 1),
          HypergeometricMass n s t x * Real.exp (l * (x : ℝ))) := hcenter
    _ ≤ Real.exp (-l * m) * Real.exp ((s : ℝ) * z) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [m, z]
      ring
