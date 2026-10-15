import Tablet.MatchingThreeEdgeSwitchProperties

-- [TABLET NODE: MatchingThreeEdgeSwitchIncoming]
theorem MatchingThreeEdgeSwitchIncoming {A B : Type*} [DecidableEq A]
    (g : A → B) (hg : Function.Injective g) (x a b₁ b₂ : A) (y : B)
    (f₁ f₂ : A → B)
    (hxa : x ≠ a) (hxb₁ : x ≠ b₁) (hab₁ : a ≠ b₁)
    (hxb₂ : x ≠ b₂) (hab₂ : a ≠ b₂)
    (hxy₁ : f₁ x = y) (hxy₂ : f₂ x = y)
    (hs₁ : MatchingThreeEdgeSwitch f₁ x a b₁ = g)
    (hs₂ : MatchingThreeEdgeSwitch f₂ x a b₂ = g) :
    b₁ = b₂ ∧ f₁ = f₂ := by
-- BODY
  obtain ⟨hx₁, ha₁, hb₁, hfix₁, _⟩ :=
    MatchingThreeEdgeSwitchProperties f₁ x a b₁ hxa hxb₁ hab₁
  obtain ⟨hx₂, ha₂, hb₂, hfix₂, _⟩ :=
    MatchingThreeEdgeSwitchProperties f₂ x a b₂ hxa hxb₂ hab₂
  rw [hs₁] at hx₁ ha₁ hb₁ hfix₁
  rw [hs₂] at hx₂ ha₂ hb₂ hfix₂
  have hb : b₁ = b₂ := hg (by rw [hb₁, hb₂, hxy₁, hxy₂])
  subst b₂
  refine ⟨rfl, ?_⟩
  funext z
  by_cases hzx : z = x
  · subst z
    exact hxy₁.trans hxy₂.symm
  by_cases hza : z = a
  · subst z
    exact hx₁.symm.trans hx₂
  by_cases hzb : z = b₁
  · subst z
    exact ha₁.symm.trans ha₂
  exact (hfix₁ z hzx hza hzb).symm.trans (hfix₂ z hzx hza hzb)
