import Tablet.Preamble
import Mathlib.Tactic.Linarith

open scoped NNReal

-- [TABLET NODE: ThinningRealParameters]
theorem ThinningRealParameters (β D ρ η ξ : ENNReal)
    (hβ : 0 < β) (hβη : β < η) (hρ : 0 < ρ) (hρD : ρ < D) (hD : D ≤ 1)
    (hξ : 0 < ξ) (hbudget : 4 * ((ρ / D) * β + ξ) ≤ η) (hsmall : 10 * η < ρ) :
    D ≠ ⊤ ∧ β ≠ ⊤ ∧ ρ ≠ ⊤ ∧ η ≠ ⊤ ∧ ξ ≠ ⊤ ∧ η < ρ ∧ β ≤ D ∧
    0 < η.toReal ∧ 0 < ξ.toReal ∧ ∃ q : ℝ≥0, q ≤ 1 ∧
      (q : ℝ) * D.toReal = ρ.toReal ∧ (q : ℝ) * β.toReal + ξ.toReal ≤ η.toReal := by
-- BODY
  have hηρ : η < ρ := by
    calc
      η = 1 * η := by simp
      _ ≤ 10 * η := mul_le_mul_left (by norm_num) _
      _ < ρ := hsmall
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top (by simp) hD
  have hρtop : ρ ≠ ⊤ := ne_top_of_lt hρD
  have hηtop : η ≠ ⊤ := ne_top_of_lt hηρ
  have hβtop : β ≠ ⊤ := ne_top_of_lt hβη
  have hξle : ξ ≤ η := by
    calc
      ξ ≤ (ρ / D) * β + ξ := le_add_left le_rfl
      _ = 1 * ((ρ / D) * β + ξ) := by simp
      _ ≤ 4 * ((ρ / D) * β + ξ) := mul_le_mul_left (by norm_num) _
      _ ≤ η := hbudget
  have hξtop : ξ ≠ ⊤ := ne_top_of_le_ne_top hηtop hξle
  have hDpos : 0 < D.toReal := ENNReal.toReal_pos (hρ.trans hρD).ne' hDtop
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos (hβ.trans hβη).ne' hηtop
  have hξpos : 0 < ξ.toReal := ENNReal.toReal_pos hξ.ne' hξtop
  let q : ℝ≥0 := ⟨ρ.toReal / D.toReal, div_nonneg ENNReal.toReal_nonneg hDpos.le⟩
  have hq : q ≤ 1 := by
    change ρ.toReal / D.toReal ≤ 1
    apply (div_le_one hDpos).mpr
    exact (ENNReal.toReal_le_toReal hρtop hDtop).mpr hρD.le
  have hqd : (q : ℝ) * D.toReal = ρ.toReal := div_mul_cancel₀ _ hDpos.ne'
  have herr : (q : ℝ) * β.toReal + ξ.toReal ≤ η.toReal := by
    have h := ENNReal.toReal_mono hηtop hbudget
    have hlambda : ρ / D ≠ ⊤ := ENNReal.div_ne_top hρtop (hρ.trans hρD).ne'
    have hprod := ENNReal.mul_ne_top hlambda hβtop
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_add hprod hξtop, ENNReal.toReal_div] at h
    change ρ.toReal / D.toReal * β.toReal + ξ.toReal ≤ η.toReal
    have hn : 0 ≤ ρ.toReal / D.toReal * β.toReal + ξ.toReal :=
      add_nonneg (mul_nonneg (div_nonneg ENNReal.toReal_nonneg hDpos.le)
        ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    linarith
  exact ⟨hDtop, hβtop, hρtop, hηtop, hξtop, hηρ,
    (hβη.trans (hηρ.trans hρD)).le, hηpos, hξpos, q, hq, hqd, herr⟩
