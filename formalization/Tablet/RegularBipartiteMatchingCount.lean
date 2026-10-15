import Tablet.PerfectMatching
import Tablet.AdjacencyPermanentMatchingCount
import Tablet.RegularMatrixNormalization
import EgorychevFalikmanFormalization.VanDerWaerdenPermanentInput
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

-- [TABLET NODE: RegularBipartiteMatchingCount]
theorem RegularBipartiteMatchingCount :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (F : SimpleGraph V) [DecidableRel F.Adj] (U W : Finset V)
      (hUW : Disjoint U W) (n k : ℕ), U.card = n → W.card = n →
      (∀ u ∈ U, (W.filter fun w => F.Adj u w).card = k) →
      (∀ w ∈ W, (U.filter fun u => F.Adj u w).card = k) →
      ((k : ENNReal) / (n : ENNReal)) ^ n * (n.factorial : ENNReal) ≤
        ({f : U → W | PerfectMatching F U W hUW f}.ncard : ENNReal) := by
-- BODY
  intro V _ _ F _ U W hUW n k hU hW hrow hcol
  classical
  by_cases hn : n = 0
  · have hUE : U = ∅ := Finset.card_eq_zero.mp (by simpa only [hn] using hU)
    have hWE : W = ∅ := Finset.card_eq_zero.mp (by simpa only [hn] using hW)
    subst U W
    have hs : {f : (∅ : Finset V) → (∅ : Finset V) |
        PerfectMatching F ∅ ∅ hUW f} = Set.univ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨⟨fun u => isEmptyElim u, fun w => isEmptyElim w⟩,
        fun u => isEmptyElim u⟩
    rw [hs, Set.ncard_univ]
    simp [hn]
  by_cases hk : k = 0
  · subst k
    simp [hn]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  let eU : U ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hU)
  let eW : W ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hW)
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    if F.Adj (eU.symm i) (eW.symm j) then 1 else 0
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    dsimp [A]
    split_ifs <;> norm_num
  have hsum (S : Finset V) (e : S ≃ Fin n) (R : V → Prop) [DecidablePred R] :
      (∑ j : Fin n, if R (e.symm j) then (1 : ℝ) else 0) =
        ((S.filter R).card : ℝ) := by
    calc
      _ = ∑ v : S, if R v then (1 : ℝ) else 0 := e.symm.sum_comp _
      _ = _ := by
        rw [Finset.sum_coe_sort S (fun v : V => if R v then (1 : ℝ) else 0),
          Finset.sum_boole]
  have hAr : ∀ i, ∑ j, A i j = (k : ℝ) := by
    intro i
    change (∑ j, if F.Adj (eU.symm i) (eW.symm j) then (1 : ℝ) else 0) = _
    rw [hsum W eW (fun w => F.Adj (eU.symm i) w), hrow _ (eU.symm i).property]
  have hAc : ∀ j, ∑ i, A i j = (k : ℝ) := by
    intro j
    change (∑ i, if F.Adj (eU.symm i) (eW.symm j) then (1 : ℝ) else 0) = _
    rw [hsum U eU (fun u => F.Adj u (eW.symm j)), hcol _ (eW.symm j).property]
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => A i j / k
  obtain ⟨hB, hBr, hBc, hscale⟩ :=
    RegularMatrixNormalization k (Nat.pos_of_ne_zero hk) A hA hAr hAc
  have hper : (n.factorial : ℝ) / (n : ℝ) ^ n ≤ Matrix.permanent B :=
    EgorychevFalikmanFormalization.VanDerWaerdenPermanentInput n B hB hBr hBc
  have hcount := AdjacencyPermanentMatchingCount F U W hUW eU eW
  have hreal : ((k : ℝ) / n) ^ n * (n.factorial : ℝ) ≤
      ({f : U → W | PerfectMatching F U W hUW f}.ncard : ℝ) := by
    calc
      _ = (k : ℝ) ^ n * ((n.factorial : ℝ) / (n : ℝ) ^ n) := by
        rw [div_pow]
        ring
      _ ≤ (k : ℝ) ^ n * Matrix.permanent B :=
        mul_le_mul_of_nonneg_left hper (pow_nonneg hkR.le _)
      _ = _ := hscale.symm.trans hcount
  have hENN := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_mul (pow_nonneg (div_nonneg hkR.le hnR.le) _),
    ENNReal.ofReal_pow (div_nonneg hkR.le hnR.le), ENNReal.ofReal_div_of_pos hnR,
    ENNReal.ofReal_natCast] using hENN
