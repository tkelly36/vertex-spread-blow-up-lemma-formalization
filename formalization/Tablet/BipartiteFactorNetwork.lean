import Tablet.FiniteCapacityNetwork

-- [TABLET NODE: BipartiteFactorNetwork]
def BipartiteFactorNetwork {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (k : ℕ) :
    FiniteCapacityNetwork (Option U ⊕ Option W) :=
-- BODY
  { source := Sum.inl none
    sink := Sum.inr none
    terminals_distinct := by simp
    capacity := fun a b => match a, b with
      | Sum.inl none, Sum.inl (some _) => k
      | Sum.inl (some u), Sum.inr (some w) => if G.Adj u.val w.val then 1 else 0
      | Sum.inr (some _), Sum.inr none => k
      | _, _ => 0 }
