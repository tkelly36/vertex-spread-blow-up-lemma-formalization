import Tablet.Preamble

-- [TABLET NODE: FiniteCapacityNetwork]
structure FiniteCapacityNetwork (V : Type*) [Fintype V] where
-- BODY
  source : V
  sink : V
  terminals_distinct : source ≠ sink
  capacity : V → V → ℕ
