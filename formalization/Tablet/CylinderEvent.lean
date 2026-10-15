import Tablet.Preamble

-- [TABLET NODE: CylinderEvent]
def CylinderEvent {X Y : Type*} {s : ℕ} (x : Fin s → X) (y : Fin s → Y) : Set (X → Y) :=
-- BODY
  {f | ∀ i, f (x i) = y i}
