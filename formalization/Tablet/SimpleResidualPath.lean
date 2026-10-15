import Tablet.FiniteIntegralFlow

-- [TABLET NODE: SimpleResidualPath]
structure SimpleResidualPath {V : Type*} [Fintype V]
    {N : FiniteCapacityNetwork V} (f : FiniteIntegralFlow N) where
-- BODY
  length : ℕ
  positive : 0 < length
  vertex : Fin (length + 1) → V
  injective : Function.Injective vertex
  start : vertex 0 = N.source
  finish : vertex (Fin.last length) = N.sink
  residual : ∀ i : Fin length,
    f.amount (vertex i.castSucc) (vertex i.succ) <
      (N.capacity (vertex i.castSucc) (vertex i.succ) : ℤ)
