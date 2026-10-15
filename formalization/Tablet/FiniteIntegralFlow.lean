import Tablet.FiniteCapacityNetwork

open scoped BigOperators

-- [TABLET NODE: FiniteIntegralFlow]
structure FiniteIntegralFlow {V : Type*} [Fintype V]
    (N : FiniteCapacityNetwork V) where
-- BODY
  amount : V → V → ℤ
  skew : ∀ v w, amount v w = -amount w v
  bound : ∀ v w, amount v w ≤ (N.capacity v w : ℤ)
  conserve : ∀ v, v ≠ N.source → v ≠ N.sink → ∑ w, amount v w = 0
