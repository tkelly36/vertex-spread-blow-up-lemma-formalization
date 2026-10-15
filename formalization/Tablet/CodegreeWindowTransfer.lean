import Tablet.Preamble

-- [TABLET NODE: CodegreeWindowTransfer]
theorem CodegreeWindowTransfer (ε p q : ENNReal) (k a c : ℕ)
    (_hε : ε ≤ 1) (_hp : p ≤ 1) (hq : q ≤ 1) (hak : a ≤ k)
    (halower : (p - ε) * k ≤ a) (haupper : (a : ENNReal) ≤ (p + ε) * k)
    (hclower : (q - ε) * a ≤ c) (hcupper : (c : ENNReal) ≤ (q + ε) * a) :
    (p * q - 2 * ε) * k ≤ c ∧ (c : ENNReal) ≤ (p * q + 2 * ε) * k := by
-- BODY
  have hk : (k : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top k
  have ha : (a : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top a
  have hak' : (a : ENNReal) ≤ k := by exact_mod_cast hak
  have hpa : p * k ≤ (a : ENNReal) + ε * k := by
    apply tsub_le_iff_right.mp
    simpa only [ENNReal.sub_mul (fun _ _ => hk)] using halower
  have hqc : q * a ≤ (c : ENNReal) + ε * a := by
    apply tsub_le_iff_right.mp
    simpa only [ENNReal.sub_mul (fun _ _ => ha)] using hclower
  have hqe : q * (ε * k) ≤ ε * k := by
    simpa only [one_mul] using mul_le_mul_right' hq (ε * k)
  constructor
  · rw [ENNReal.sub_mul (fun _ _ => hk)]
    apply tsub_le_iff_right.mpr
    calc
      p * q * k = q * (p * k) := by ring
      _ ≤ q * ((a : ENNReal) + ε * k) := mul_le_mul_left' hpa q
      _ = q * a + q * (ε * k) := mul_add _ _ _
      _ ≤ ((c : ENNReal) + ε * a) + ε * k := add_le_add hqc hqe
      _ ≤ ((c : ENNReal) + ε * k) + ε * k :=
        add_le_add (add_le_add le_rfl (mul_le_mul_left' hak' ε)) le_rfl
      _ = (c : ENNReal) + 2 * ε * k := by ring
  · calc
      (c : ENNReal) ≤ (q + ε) * a := hcupper
      _ = q * a + ε * a := add_mul _ _ _
      _ ≤ q * ((p + ε) * k) + ε * k :=
        add_le_add (mul_le_mul_left' haupper q) (mul_le_mul_left' hak' ε)
      _ = p * q * k + q * (ε * k) + ε * k := by ring
      _ ≤ p * q * k + ε * k + ε * k := add_le_add (add_le_add le_rfl hqe) le_rfl
      _ = (p * q + 2 * ε) * k := by ring
