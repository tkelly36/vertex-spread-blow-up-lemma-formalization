import Tablet.PerfectMatching
import Tablet.MatchingThreeEdgeSwitchProperties

-- [TABLET NODE: MatchingThreeEdgeSwitchValid]
theorem MatchingThreeEdgeSwitchValid {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U W : Finset V) (hUW : Disjoint U W)
    (f : U → W) (hf : PerfectMatching G U W hUW f)
    (x a b : U) (y : W) (hxy : f x = y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (h₁ : G.Adj x (f a)) (h₂ : G.Adj a (f b)) (h₃ : G.Adj b (f x))
    {I : Type*} (xN : I → U) (yN : I → W)
    (hN : ∀ i, f (xN i) = yN i)
    (hNx : ∀ i, xN i ≠ x) (hNa : ∀ i, xN i ≠ a) (hNb : ∀ i, xN i ≠ b) :
    let g := MatchingThreeEdgeSwitch f x a b
    PerfectMatching G U W hUW g ∧ (∀ i, g (xN i) = yN i) ∧ g x ≠ y := by
-- BODY
  dsimp only
  obtain ⟨hx, ha, hb, hfix, hbij⟩ :=
    MatchingThreeEdgeSwitchProperties f x a b hxa hxb hab
  refine ⟨⟨hbij hf.1, ?_⟩, ?_, ?_⟩
  · intro z
    by_cases hzx : z = x
    · subst z
      rw [hx]
      exact h₁
    by_cases hza : z = a
    · subst z
      rw [ha]
      exact h₂
    by_cases hzb : z = b
    · subst z
      rw [hb]
      exact h₃
    rw [hfix z hzx hza hzb]
    exact hf.2 z
  · intro i
    rw [hfix (xN i) (hNx i) (hNa i) (hNb i)]
    exact hN i
  · rw [hx, ← hxy]
    exact fun h => hxa (hf.1.1 h).symm
