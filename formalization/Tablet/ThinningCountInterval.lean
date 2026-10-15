import Tablet.Preamble
import Mathlib.Tactic.Linarith

-- [TABLET NODE: ThinningCountInterval]
theorem ThinningCountInterval (d ε ρ η : ENNReal)
    (hd : d ≠ ⊤) (hε : ε ≠ ⊤) (hρ : ρ ≠ ⊤) (hη : η ≠ ⊤)
    (hεd : ε ≤ d) (hηρ : η ≤ ρ) (q ξ : ℝ) (hq : 0 ≤ q)
    (hqd : q * d.toReal = ρ.toReal) (herr : q * ε.toReal + ξ ≤ η.toReal)
    (m a b : ℕ)
    (hold : (d - ε) * m ≤ (a : ENNReal) ∧ (a : ENNReal) ≤ (d + ε) * m)
    (hdev : |(b : ℝ) - q * a| ≤ ξ * m) :
    (ρ - η) * m ≤ (b : ENNReal) ∧ (b : ENNReal) ≤ (ρ + η) * m := by
-- BODY
  have hlo := ENNReal.toReal_mono (by simp) hold.1
  have hhi := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hd, hε⟩) (by simp)) hold.2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_sub_of_le hεd hd, ENNReal.toReal_add hd hε] at hlo hhi
  have hab := abs_le.mp hdev
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hql := mul_le_mul_of_nonneg_left hlo hq
  have hqu := mul_le_mul_of_nonneg_left hhi hq
  have he := mul_le_mul_of_nonneg_right herr hm
  have hl : (ρ.toReal - η.toReal) * m ≤ (b : ℝ) := by nlinarith
  have hu : (b : ℝ) ≤ (ρ.toReal + η.toReal) * m := by nlinarith
  constructor
  · apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ENNReal.sub_ne_top hρ) (by simp)) (by simp)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_sub_of_le hηρ hρ] using hl
  · apply (ENNReal.toReal_le_toReal (by simp)
      (ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hρ, hη⟩) (by simp))).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_add hρ hη] using hu
