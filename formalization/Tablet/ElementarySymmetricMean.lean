import Tablet.Preamble
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Tablet.ElementarySymmetricExtremaStep
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Monoid

open scoped BigOperators Topology
open Filter

-- [TABLET NODE: ElementarySymmetricMean]
theorem ElementarySymmetricMean (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ A, a i) /
      (n.choose k : ℝ) ≤ ((∑ i, a i) / (n : ℝ)) ^ k := by
-- BODY
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [Finset.powersetCard_zero]
  by_cases hk1 : k = 1
  · subst k
    simp [Finset.powersetCard_one]
  by_cases hn1 : n = 1
  · omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let E (x : Fin n → ℝ) : ℝ :=
    ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, x t
  let c := (∑ t, a t) / (n : ℝ)
  let q := 1 - 1 / (2 * (n : ℝ))
  have hq0 : 0 ≤ q := by
    have h : 1 / (2 * (n : ℝ)) ≤ 1 :=
      (div_le_one (by positivity : 0 < 2 * (n : ℝ))).2 (by linarith)
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    have h : 0 < 1 / (2 * (n : ℝ)) := by positivity
    dsimp [q]
    linarith
  -- Iterate within the subtype of nonnegative vectors.
  let step (x : {x : Fin n → ℝ // ∀ t, 0 ≤ x t}) :
      {x : Fin n → ℝ // ∀ t, 0 ≤ x t} :=
    ⟨Classical.choose (ElementarySymmetricExtremaStep n k hn x.val x.property),
      (Classical.choose_spec (ElementarySymmetricExtremaStep n k hn x.val x.property)).2.1⟩
  let f : ℕ → {x : Fin n → ℝ // ∀ t, 0 ≤ x t} :=
    Nat.rec ⟨a, ha⟩ (fun _ x => step x)
  let v (r : ℕ) : Fin n → ℝ := (f r).val
  have hv0 : v 0 = a := rfl
  have htransition (r : ℕ) :
      (∑ t, v (r + 1) t) = (∑ t, v r t) ∧
      E (v r) ≤ E (v (r + 1)) ∧
      (∑ t, (v (r + 1) t - (∑ u, v r u) / (n : ℝ)) ^ 2) ≤
        q * (∑ t, (v r t - (∑ u, v r u) / (n : ℝ)) ^ 2) :=
    (Classical.choose_spec (ElementarySymmetricExtremaStep n k hn (f r).val (f r).property)).2.2
  have hsum (r : ℕ) : (∑ t, v r t) = ∑ t, a t := by
    induction r with
    | zero => rw [hv0]
    | succ r ih => exact (htransition r).1.trans ih
  have hE (r : ℕ) : E a ≤ E (v r) := by
    induction r with
    | zero => rw [hv0]
    | succ r ih => exact ih.trans (htransition r).2.1
  let V (r : ℕ) : ℝ := ∑ t, (v r t - c) ^ 2
  have hV0 (r : ℕ) : 0 ≤ V r := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hVstep (r : ℕ) : V (r + 1) ≤ q * V r := by
    simpa only [hsum r] using (htransition r).2.2
  have hVbound (r : ℕ) : V r ≤ q ^ r * V 0 := by
    induction r with
    | zero => simp
    | succ r ih =>
      calc
        V (r + 1) ≤ q * V r := hVstep r
        _ ≤ q * (q ^ r * V 0) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (r + 1) * V 0 := by rw [pow_succ]; ring
  have hgeom : Tendsto (fun r : ℕ => q ^ r * V 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (V 0)
  have hVlim : Tendsto V atTop (𝓝 0) := squeeze_zero hV0 hVbound hgeom
  have hsqrt : Tendsto (fun r => Real.sqrt (V r)) atTop (𝓝 0) := by
    simpa using hVlim.sqrt
  have hcoord (t : Fin n) : Tendsto (fun r => v r t) atTop (𝓝 c) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    have hb (r : ℕ) : |v r t - c| ≤ Real.sqrt (V r) := by
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      exact Finset.single_le_sum (fun u _ => sq_nonneg (v r u - c)) (Finset.mem_univ t)
    exact squeeze_zero (fun r => abs_nonneg _) hb hsqrt
  -- Pass coordinate limits through the finite products and finite sum.
  have hElim : Tendsto (fun r => E (v r)) atTop (𝓝 (E (fun _ => c))) := by
    exact tendsto_finset_sum _ fun A _ => tendsto_finset_prod A fun t _ => hcoord t
  have heconst : E (fun _ => c) = (n.choose k : ℝ) * c ^ k := by
    dsimp [E]
    calc
      _ = ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, c ^ k := by
        refine Finset.sum_congr rfl ?_
        intro A hA
        simp [Finset.prod_const, (Finset.mem_powersetCard.mp hA).2]
      _ = _ := by simp
  have he : E a ≤ (n.choose k : ℝ) * c ^ k := by
    rw [← heconst]
    exact ge_of_tendsto hElim (Eventually.of_forall hE)
  have hchoose : 0 < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  exact (div_le_iff₀ hchoose).2 (by simpa [E, c, mul_comm] using he)
