import Tablet.CylinderEvent

-- [TABLET NODE: VertexSpreadOn]
def VertexSpreadOn {X Y : Type*} (μ : PMF (X → Y)) (q : ENNReal) (U : Set Y) : Prop :=
-- BODY
  q ≤ 1 ∧ ∀ (s : ℕ) (x : Fin s → X) (y : Fin s → Y),
    Function.Injective x → (∀ i, y i ∈ U) →
      μ.toOuterMeasure (CylinderEvent x y) ≤ q ^ s
