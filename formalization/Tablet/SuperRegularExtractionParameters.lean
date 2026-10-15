import Tablet.RegularExtractionParameters
import Tablet.ExtractionTailCutoffs

-- [TABLET NODE: SuperRegularExtractionParameters]
theorem SuperRegularExtractionParameters (η d : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hd : 0 < d) (hd1 : d < 1) :
    ∃ h γ α ε : ℝ, ∃ l M n₀ : ℕ,
      0 < h ∧ h ≤ 1 / 100 ∧ h ≤ (d ^ 2 / 2) / 100 ∧
      h ≤ η ^ 2 / 1000 ∧ 3 * h < η ∧ 4 * h < η ∧
      2 * h + 4 * h / η < η ∧
      0 < γ ∧ γ ≤ 1 ∧ 0 < α ∧ α ≤ γ ∧ α ≤ γ ^ 2 ∧
      0 < ε ∧ ε < η ∧ ε * M < γ ∧
      1 ≤ l ∧ l ≤ M ∧ SzemerediRegularity.bound α l ≤ M ∧
      1 ≤ n₀ ∧ M ≤ n₀ ∧
      2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2 < h / 4 ∧
      ∀ n : ℕ, n₀ ≤ n →
        1 ≤ h * (n : ℝ) ∧
        4 * n * Real.exp (-(d ^ 2 / 2) ^ 2 * (n : ℝ) / 8) < 1 / 4 ∧
        2 * (4 : ℝ) ^ n * Real.exp (-h ^ 4 * (n : ℝ) ^ 2 / 8) < 1 / 4 ∧
        4 * n * Real.exp (-2 * h ^ 2 * (n : ℝ)) < 1 / 4 ∧
        2 * (4 : ℝ) ^ n * Real.exp (-2 * h ^ 4 * (n : ℝ) ^ 2) < 1 / 4 := by
-- BODY
  let θ := min η (min ((d ^ 2 / 2) / 100) (η ^ 2 / 1000))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθη : θ ≤ η := min_le_left _ _
  have hθ1 : θ < 1 := hθη.trans_lt hη1
  obtain ⟨h, γ, α, ε, l, M, _, hh, hhθ, hh100, hγ, hγ1, hα,
    hαγ, hαγγ, hε, hεθ, hεM, hl, hlM, hbound, _, _, hmargin, _⟩ :=
    RegularExtractionParameters θ hθ hθ1
  have hhc : h ≤ (d ^ 2 / 2) / 100 := hhθ.le.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hhη : h ≤ η ^ 2 / 1000 := hhθ.le.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hηsq : η ^ 2 ≤ η := by nlinarith only [hη, hη1]
  have h3 : 3 * h < η := by nlinarith only [hhη, hηsq, hη]
  have h4 : 4 * h < η := by nlinarith only [hhη, hηsq, hη]
  have hdiv : 4 * h / η ≤ 4 * η / 1000 := by
    apply (div_le_iff₀ hη).mpr
    nlinarith only [hhη]
  have hfinal : 2 * h + 4 * h / η < η := by
    nlinarith only [hhη, hηsq, hdiv, hη]
  obtain ⟨n₀, hn₀, hMn₀, hcut⟩ :=
    ExtractionTailCutoffs (d ^ 2 / 2) h M (by positivity) hh
  exact ⟨h, γ, α, ε, l, M, n₀, hh, hh100, hhc, hhη, h3, h4, hfinal,
    hγ, hγ1, hα, hαγ, hαγγ, hε, hεθ.trans_le hθη, hεM,
    hl, hlM, hbound, hn₀, hMn₀, hmargin, hcut⟩
