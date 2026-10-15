import Tablet.MatchingThreeEdgeSwitch

-- [TABLET NODE: MatchingThreeEdgeSwitchProperties]
theorem MatchingThreeEdgeSwitchProperties {A B : Type*} [DecidableEq A]
    (f : A → B) (x a b : A) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) :
    let g := MatchingThreeEdgeSwitch f x a b
    g x = f a ∧ g a = f b ∧ g b = f x ∧
      (∀ z, z ≠ x → z ≠ a → z ≠ b → g z = f z) ∧
      (Function.Bijective f → Function.Bijective g) := by
-- BODY
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [MatchingThreeEdgeSwitch, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  · simp [MatchingThreeEdgeSwitch, Equiv.swap_apply_of_ne_of_ne hxb.symm hab.symm]
  · simp [MatchingThreeEdgeSwitch]
  · intro z hzx hza hzb
    simp [MatchingThreeEdgeSwitch, Equiv.swap_apply_of_ne_of_ne hza hzb,
      Equiv.swap_apply_of_ne_of_ne hzx hza]
  · intro hf
    exact hf.comp ((Equiv.swap x a).bijective.comp (Equiv.swap a b).bijective)
