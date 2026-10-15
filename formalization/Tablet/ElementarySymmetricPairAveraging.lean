import Tablet.Preamble
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

-- [TABLET NODE: ElementarySymmetricPairAveraging]
theorem ElementarySymmetricPairAveraging (n k : ℕ) (a : Fin n → ℝ)
    (ha : ∀ t, 0 ≤ a t) (i j : Fin n) (hij : i ≠ j) :
    let m := (a i + a j) / 2
    let b := Function.update (Function.update a i m) j m
    (∀ t, 0 ≤ b t) ∧ (∑ t, b t) = (∑ t, a t) ∧
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, a t) ≤
        (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, b t) ∧
      (∀ c : ℝ, (∑ t, (b t - c) ^ 2) =
        (∑ t, (a t - c) ^ 2) - (a i - a j) ^ 2 / 2) := by
-- BODY
  classical
  dsimp only
  let m := (a i + a j) / 2
  let b := Function.update (Function.update a i m) j m
  let s := ((Finset.univ : Finset (Fin n)).erase i).erase j
  have hi : i ∉ s := by simp [s]
  have hj : j ∉ s := by simp [s]
  have hjs : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  have huniv : (Finset.univ : Finset (Fin n)) = insert i (insert j s) := by
    rw [Finset.insert_erase hjs, Finset.insert_erase (Finset.mem_univ i)]
  have hbi : b i = m := by simp [b, hij]
  have hbj : b j = m := by simp [b]
  have hba (t : Fin n) (ht : t ∈ s) : b t = a t := by
    have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    have htj : t ≠ j := (Finset.mem_erase.mp ht).1
    simp [b, hti, htj]
  have sum_split (f : Fin n → ℝ) :
      (∑ t, f t) = f i + f j + ∑ t ∈ s, f t := by
    rw [huniv, Finset.sum_insert (by simp [hi, hij]), Finset.sum_insert hj]
    ring
  have hsum : (∑ t, b t) = (∑ t, a t) := by
    rw [sum_split b, sum_split a, hbi, hbj]
    have hs : (∑ t ∈ s, b t) = ∑ t ∈ s, a t := Finset.sum_congr rfl hba
    rw [hs]
    dsimp [m]
    ring
  have hnonneg : ∀ t, 0 ≤ b t := by
    intro t
    by_cases htj : t = j
    · subst t; rw [hbj]; exact div_nonneg (add_nonneg (ha i) (ha j)) (by norm_num)
    by_cases hti : t = i
    · subst t; rw [hbi]; exact div_nonneg (add_nonneg (ha i) (ha j)) (by norm_num)
    simpa [b, hti, htj] using ha t
  have recur (u : Finset (Fin n)) (x : Fin n) (hx : x ∉ u)
      (r : ℕ) (f : Fin n → ℝ) :
      (∑ A ∈ (insert x u).powersetCard (r + 1), ∏ t ∈ A, f t) =
        (∑ A ∈ u.powersetCard (r + 1), ∏ t ∈ A, f t) +
          f x * (∑ A ∈ u.powersetCard r, ∏ t ∈ A, f t) := by
    rw [Finset.powersetCard_succ_insert hx]
    have hnot (A : Finset (Fin n)) (hA : A ∈ u.powersetCard r) : x ∉ A :=
      fun h => hx ((Finset.mem_powersetCard.mp hA).1 h)
    rw [Finset.sum_union]
    · rw [Finset.sum_image]
      · congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun A hA => Finset.prod_insert (hnot A hA)
      · intro A hA B hB hAB
        have := congrArg (fun A => A.erase x) hAB
        simpa [Finset.erase_insert (hnot A hA), Finset.erase_insert (hnot B hB)] using this
    · refine Finset.disjoint_left.mpr ?_
      intro A hA hB
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB
      exact hx ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self x B))
  have e_same (r : ℕ) :
      (∑ A ∈ s.powersetCard r, ∏ t ∈ A, b t) =
        (∑ A ∈ s.powersetCard r, ∏ t ∈ A, a t) := by
    refine Finset.sum_congr rfl ?_
    intro A hA
    exact Finset.prod_congr rfl fun t ht => hba t ((Finset.mem_powersetCard.mp hA).1 ht)
  have hmono :
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, a t) ≤
        (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, b t) := by
    rcases k with _ | k
    · simp [Finset.powersetCard_zero]
    rcases k with _ | r
    · simpa [Finset.powersetCard_one] using hsum.ge
    have decomposition (f : Fin n → ℝ) :
        (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard (r + 1 + 1), ∏ t ∈ A, f t) =
          (∑ A ∈ s.powersetCard (r + 1 + 1), ∏ t ∈ A, f t) +
          (f i + f j) * (∑ A ∈ s.powersetCard (r + 1), ∏ t ∈ A, f t) +
          f i * f j * (∑ A ∈ s.powersetCard r, ∏ t ∈ A, f t) := by
      rw [huniv, recur (insert j s) i (by simp [hi, hij]),
        recur s j hj, recur s j hj]
      ring
    rw [decomposition a, decomposition b, hbi, hbj, e_same, e_same, e_same]
    have hE : 0 ≤ ∑ A ∈ s.powersetCard r, ∏ t ∈ A, a t :=
      Finset.sum_nonneg fun A _ => Finset.prod_nonneg fun t _ => ha t
    have hprod : a i * a j ≤ m * m := by
      dsimp [m]
      nlinarith [sq_nonneg (a i - a j)]
    have hm : m + m = a i + a j := by dsimp [m]; ring
    rw [hm]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hprod hE) _
  refine ⟨hnonneg, hsum, hmono, ?_⟩
  intro c
  change (∑ t, (b t - c) ^ 2) = (∑ t, (a t - c) ^ 2) - (a i - a j) ^ 2 / 2
  rw [sum_split, sum_split, hbi, hbj]
  have hs : (∑ t ∈ s, (b t - c) ^ 2) = ∑ t ∈ s, (a t - c) ^ 2 :=
    Finset.sum_congr rfl fun t ht => by rw [hba t ht]
  rw [hs]
  dsimp [m]
  ring
