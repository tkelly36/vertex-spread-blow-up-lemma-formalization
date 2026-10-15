import Tablet.Preamble

-- [TABLET NODE: SmallNeighborhoodCodegreeWindow]
theorem SmallNeighborhoodCodegreeWindow (ε p q : ENNReal) (k a c : ℕ)
    (hk : k ≠ 0) (_hε : ε ≤ 1) (_hp : p ≤ 1) (hq : q ≤ 1)
    (halower : (p - ε) * k ≤ a) (hasmall : (a : ENNReal) ≤ ε * k)
    (hca : c ≤ a) :
    (p * q - 2 * ε) * k ≤ c ∧ (c : ENNReal) ≤ (p * q + 2 * ε) * k := by
-- BODY
  have hkfinite : (k : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top k
  have hkzero : (k : ENNReal) ≠ 0 := by exact_mod_cast hk
  have hp : p ≤ 2 * ε := by
    have hpk : p * k ≤ 2 * ε * k := by
      calc
        p * k ≤ (a : ENNReal) + ε * k := by
          apply tsub_le_iff_right.mp
          simpa only [ENNReal.sub_mul (fun _ _ => hkfinite)] using halower
        _ ≤ ε * k + ε * k := add_le_add hasmall le_rfl
        _ = 2 * ε * k := by ring
    exact (ENNReal.mul_le_mul_right hkzero hkfinite).mp hpk
  have hpq : p * q ≤ 2 * ε := by
    have hpq' : p * q ≤ p := by simpa only [mul_one] using mul_le_mul_left' hq p
    exact hpq'.trans hp
  constructor
  · simp only [tsub_eq_zero_of_le hpq, zero_mul, zero_le]
  · calc
      (c : ENNReal) ≤ a := by exact_mod_cast hca
      _ ≤ ε * k := hasmall
      _ ≤ (p * q + 2 * ε) * k := by
        apply mul_le_mul_right'
        calc
          ε ≤ ε + ε := le_add_right le_rfl
          _ = 2 * ε := by ring
          _ ≤ p * q + 2 * ε := le_add_left le_rfl
