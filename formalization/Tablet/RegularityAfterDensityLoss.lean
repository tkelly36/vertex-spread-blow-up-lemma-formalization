import Tablet.RegularPair

-- [TABLET NODE: RegularityAfterDensityLoss]
theorem RegularityAfterDensityLoss :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (W₁ W₂ : Finset V) (ε δ η ρ : ENNReal),
      ε ≤ η → ε + ρ ≤ η → RegularPair G W₁ W₂ ε δ →
      (∀ U ⊆ W₁, ∀ W ⊆ W₂,
        η * W₁.card < U.card → η * W₂.card < W.card →
        PairDensity H U W ≤ PairDensity G U W ∧
        PairDensity G U W - PairDensity H U W ≤ ρ) →
      RegularPair H W₁ W₂ η δ := by
-- BODY
  intro V _ _ G H _ _ W₁ W₂ ε δ η ρ hε hsum hreg hloss
  unfold RegularPair at hreg ⊢
  intro U hU W hW hsizeU hsizeW
  have hsizeUε : ε * (W₁.card : ENNReal) < (U.card : ENNReal) :=
    (mul_le_mul_right' hε (W₁.card : ENNReal)).trans_lt hsizeU
  have hsizeWε : ε * (W₂.card : ENNReal) < (W.card : ENNReal) :=
    (mul_le_mul_right' hε (W₂.card : ENNReal)).trans_lt hsizeW
  obtain ⟨hlower, hupper⟩ := hreg U hU W hW hsizeUε hsizeWε
  obtain ⟨hmono, hbounded⟩ := hloss U hU W hW hsizeU hsizeW
  constructor
  · calc
      δ - η ≤ δ - (ε + ρ) := tsub_le_tsub_left hsum δ
      _ = (δ - ε) - ρ := (tsub_tsub δ ε ρ).symm
      _ ≤ PairDensity G U W - ρ := tsub_le_tsub_right hlower ρ
      _ ≤ PairDensity H U W := tsub_le_iff_tsub_le.mp hbounded
  · exact hmono.trans (hupper.trans (add_le_add le_rfl hε))
