import Tablet.VertexSpreadOn

-- [TABLET NODE: VertexSpreadRestriction]
theorem VertexSpreadRestriction {X X' Y : Type*} {μ : PMF (X → Y)} {q : ENNReal}
    {U : Set Y} (e : X' ↪ X) (hμ : VertexSpreadOn μ q U) :
    VertexSpreadOn (μ.map (fun f => f ∘ e)) q U := by
-- BODY
  refine ⟨hμ.1, ?_⟩
  intro s x y hx hy
  rw [PMF.toOuterMeasure_map_apply]
  change μ.toOuterMeasure (CylinderEvent (e ∘ x) y) ≤ q ^ s
  exact hμ.2 s (e ∘ x) y (e.injective.comp hx) hy
