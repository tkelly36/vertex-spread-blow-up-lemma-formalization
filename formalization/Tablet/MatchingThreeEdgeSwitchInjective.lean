import Tablet.MatchingThreeEdgeSwitchProperties

-- [TABLET NODE: MatchingThreeEdgeSwitchInjective]
theorem MatchingThreeEdgeSwitchInjective {A B : Type*} [DecidableEq A]
    (f : A → B) (hf : Function.Bijective f) (x : A) :
    Function.Injective (fun p : {p : A × A // x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2} =>
      MatchingThreeEdgeSwitch f x p.val.1 p.val.2) := by
-- BODY
  intro p q hpq
  dsimp only at hpq
  obtain ⟨hpx, _, hpb, _, hpg⟩ :=
    MatchingThreeEdgeSwitchProperties f x p.val.1 p.val.2
      p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨hqx, _, hqb, _, _⟩ :=
    MatchingThreeEdgeSwitchProperties f x q.val.1 q.val.2
      q.property.1 q.property.2.1 q.property.2.2
  have ha : p.val.1 = q.val.1 := hf.1 (by
    rw [← hpx, ← hqx]
    exact congrFun hpq x)
  have hb : p.val.2 = q.val.2 := (hpg hf).1 (by
    rw [hpb, hpq, hqb])
  exact Subtype.ext (Prod.ext ha hb)
