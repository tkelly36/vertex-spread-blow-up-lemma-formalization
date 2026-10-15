import Tablet.AdjacencyPermanentMatchingCount
import EntropyMethodsFormalization.BregmanMinc
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators

-- [TABLET NODE: BregmanMatchingDegreeProduct]
theorem BregmanMatchingDegreeProduct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V)
    (hST : Disjoint S T) {y : ℕ} (eS : S ≃ Fin y) (eT : T ≃ Fin y) :
    ((∃ i : Fin y, (T.filter fun w => G.Adj (eS.symm i) w).card = 0) →
      {f : S → T | PerfectMatching G S T hST f}.ncard = 0) ∧
    ((∀ i : Fin y, 0 < (T.filter fun w => G.Adj (eS.symm i) w).card) →
      ({f : S → T | PerfectMatching G S T hST f}.ncard : ℝ) ≤
        ∏ i : Fin y, Real.rpow
          ((T.filter fun w => G.Adj (eS.symm i) w).card.factorial : ℝ)
          (((T.filter fun w => G.Adj (eS.symm i) w).card : ℝ)⁻¹)) := by
-- BODY
  classical
  let A : Matrix (Fin y) (Fin y) ℕ := fun i j =>
    if G.Adj (eS.symm i) (eT.symm j) then 1 else 0
  have h01 : EntropyMethodsFormalization.ZeroOneMatrix A := by
    intro i j
    dsimp [A]
    split_ifs <;> simp
  have hrow (i : Fin y) :
      (EntropyMethodsFormalization.BregmanRowSupport A i).card =
        (T.filter fun w => G.Adj (eS.symm i) w).card := by
    have hs : (∑ j : Fin y, if G.Adj (eS.symm i) (eT.symm j) then (1 : ℕ) else 0) =
        (T.filter fun w => G.Adj (eS.symm i) w).card := by
      calc
        _ = ∑ w : T, if G.Adj (eS.symm i) w then (1 : ℕ) else 0 :=
          eT.symm.sum_comp _
        _ = _ := by
          rw [Finset.sum_coe_sort T (fun w : V =>
            if G.Adj (eS.symm i) w then (1 : ℕ) else 0), Finset.sum_boole]
          simp
    have he : EntropyMethodsFormalization.BregmanRowSupport A i =
        Finset.univ.filter (fun j => G.Adj (eS.symm i) (eT.symm j)) := by
      ext j
      by_cases h : G.Adj (eS.symm i) (eT.symm j) <;>
        simp [EntropyMethodsFormalization.BregmanRowSupport, A, h]
    rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact hs
  have hcast : ((Matrix.permanent A : ℕ) : ℝ) =
      Matrix.permanent (fun i j : Fin y =>
        if G.Adj (eS.symm i) (eT.symm j) then (1 : ℝ) else 0) := by
    simp only [Matrix.permanent, Nat.cast_sum, Nat.cast_prod, A]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  have hcount : Matrix.permanent A =
      {f : S → T | PerfectMatching G S T hST f}.ncard := by
    exact_mod_cast hcast.trans (AdjacencyPermanentMatchingCount G S T hST eS eT)
  have hbound := EntropyMethodsFormalization.BregmanMinc A h01
  constructor
  · intro hz
    rw [← hcount]
    apply hbound.1
    simpa only [hrow] using hz
  · intro hp
    have h := hbound.2 (by simpa only [hrow] using hp)
    simpa only [hrow, hcount] using h
