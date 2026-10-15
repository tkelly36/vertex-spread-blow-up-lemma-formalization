import Tablet.PerfectMatching
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Set.Card

open scoped BigOperators

-- [TABLET NODE: AdjacencyPermanentMatchingCount]
theorem AdjacencyPermanentMatchingCount {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (U W : Finset V)
    (hUW : Disjoint U W) {n : ℕ} (eU : U ≃ Fin n) (eW : W ≃ Fin n) :
    Matrix.permanent (fun i j : Fin n =>
      if F.Adj (eU.symm i) (eW.symm j) then (1 : ℝ) else 0) =
    ({f : U → W | PerfectMatching F U W hUW f}.ncard : ℝ) := by
-- BODY
  classical
  let P : Equiv.Perm (Fin n) → Prop := fun σ =>
    ∀ i, F.Adj (eU.symm i) (eW.symm (σ i))
  let E : {σ : Equiv.Perm (Fin n) // P σ} ≃
      {f : U → W // PerfectMatching F U W hUW f} :=
    { toFun := fun σ => ⟨fun u => eW.symm (σ.val (eU u)),
        ⟨(eU.trans (σ.val.trans eW.symm)).bijective, fun u => by
          simpa using σ.property (eU u)⟩⟩
      invFun := fun f => ⟨eU.symm.trans ((Equiv.ofBijective f.val f.property.1).trans eW),
        fun i => by simpa using f.property.2 (eU.symm i)⟩
      left_inv := by
        intro σ
        apply Subtype.ext
        apply Equiv.ext
        intro i
        simp
      right_inv := by
        intro f
        apply Subtype.ext
        funext u
        simp }
  have hterm (σ : Equiv.Perm (Fin n)) :
      (∏ i, if F.Adj (eU.symm i) (eW.symm (σ i)) then (1 : ℝ) else 0) =
        if P σ then 1 else 0 := by
    by_cases h : P σ
    · rw [if_pos h]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hcard : {f : U → W | PerfectMatching F U W hUW f}.ncard =
      (Finset.univ.filter P).card := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact (Fintype.card_congr E).symm.trans (Fintype.card_subtype P)
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  simp only [Matrix.transpose_apply]
  simp_rw [hterm]
  rw [Finset.sum_boole, hcard]
