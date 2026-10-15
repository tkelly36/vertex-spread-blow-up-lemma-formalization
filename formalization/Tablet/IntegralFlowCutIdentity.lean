import Tablet.FiniteIntegralFlow

open scoped BigOperators

-- [TABLET NODE: IntegralFlowCutIdentity]
theorem IntegralFlowCutIdentity {V : Type*} [Fintype V] [DecidableEq V]
    {N : FiniteCapacityNetwork V} (f : FiniteIntegralFlow N)
    (S : Finset V) (hs : N.source ∈ S) (ht : N.sink ∉ S) :
    (∑ w, f.amount N.source w) =
      ∑ v ∈ S, ∑ w ∈ Finset.univ \ S, f.amount v w := by
-- BODY
  have hcancel : (∑ v ∈ S, ∑ w ∈ S, f.amount v w) =
      -(∑ v ∈ S, ∑ w ∈ S, f.amount v w) := by
    calc
      _ = ∑ w ∈ S, ∑ v ∈ S, f.amount v w := Finset.sum_comm
      _ = ∑ w ∈ S, ∑ v ∈ S, -f.amount w v := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro v hv
        exact f.skew v w
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hz : (∑ v ∈ S, ∑ w ∈ S, f.amount v w) = 0 := by omega
  have hdiv : (∑ v ∈ S, ∑ w, f.amount v w) = ∑ w, f.amount N.source w := by
    apply Finset.sum_eq_single N.source
    · intro v hv hne
      exact f.conserve v hne (fun he => ht (he ▸ hv))
    · intro hnot
      exact (hnot hs).elim
  have hsplit : (∑ v ∈ S, ∑ w, f.amount v w) =
      (∑ v ∈ S, ∑ w ∈ S, f.amount v w) +
      ∑ v ∈ S, ∑ w ∈ Finset.univ \ S, f.amount v w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    have h := Finset.sum_sdiff (f := f.amount v) (Finset.subset_univ S)
    simpa only [add_comm] using h.symm
  rw [hz, zero_add, hdiv] at hsplit
  exact hsplit
