import Tablet.VertexSpreadOn

-- [TABLET NODE: VertexSpreadMonotone]
theorem VertexSpreadMonotone {X Y : Type*} {μ : PMF (X → Y)} {q q' : ENNReal}
    {U : Set Y} (hμ : VertexSpreadOn μ q U) (hqq' : q ≤ q') (hq' : q' ≤ 1) :
    VertexSpreadOn μ q' U := by
-- BODY
  refine ⟨hq', fun s x y hx hy => ?_⟩
  exact (hμ.2 s x y hx hy).trans (pow_le_pow_left' hqq' s)
