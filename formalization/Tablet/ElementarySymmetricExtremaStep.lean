import Tablet.ElementarySymmetricPairAveraging
import Mathlib.Data.Finset.Max

open scoped BigOperators

-- [TABLET NODE: ElementarySymmetricExtremaStep]
theorem ElementarySymmetricExtremaStep (n k : ℕ) (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ t, 0 ≤ a t) :
    ∃ b : Fin n → ℝ,
      (((∀ s t, a s = a t) ∧ b = a) ∨
        ∃ i j : Fin n, i ≠ j ∧ (∀ t, a i ≤ a t) ∧ (∀ t, a t ≤ a j) ∧
          a i < a j ∧
          b = Function.update (Function.update a i ((a i + a j) / 2)) j
            ((a i + a j) / 2)) ∧
      (∀ t, 0 ≤ b t) ∧ (∑ t, b t) = (∑ t, a t) ∧
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, a t) ≤
        (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ t ∈ A, b t) ∧
      (∑ t, (b t - (∑ u, a u) / (n : ℝ)) ^ 2) ≤
        (1 - 1 / (2 * (n : ℝ))) *
          (∑ t, (a t - (∑ u, a u) / (n : ℝ)) ^ 2) := by
-- BODY
  classical
  let c := (∑ t, a t) / (n : ℝ)
  let t0 : Fin n := ⟨0, hn⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  by_cases hconst : ∀ t, a t = a t0
  · have hc : c = a t0 := by
      simp [c, hconst, ne_of_gt hnR]
    refine ⟨a, Or.inl ⟨?_, rfl⟩, ha, rfl, le_rfl, ?_⟩
    · intro s t
      rw [hconst s, hconst t]
    change (∑ t, (a t - c) ^ 2) ≤ (1 - 1 / (2 * (n : ℝ))) * (∑ t, (a t - c) ^ 2)
    simp [hc, hconst]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨t0, Finset.mem_univ t0⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ a hne
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ a hne
  have hmin (t : Fin n) : a i ≤ a t := hi t (Finset.mem_univ t)
  have hmax (t : Fin n) : a t ≤ a j := hj t (Finset.mem_univ t)
  have hij : i ≠ j := by
    intro heq
    apply hconst
    have he (t : Fin n) : a t = a i := le_antisymm (heq ▸ hmax t) (hmin t)
    intro t
    rw [he t, he t0]
  have hlt : a i < a j := by
    apply lt_of_le_of_ne (hmin j)
    intro heq
    apply hconst
    have he (t : Fin n) : a t = a i := le_antisymm (heq ▸ hmax t) (hmin t)
    intro t
    rw [he t, he t0]
  let b := Function.update (Function.update a i ((a i + a j) / 2)) j ((a i + a j) / 2)
  obtain ⟨hb, hsum, he, hvar⟩ := ElementarySymmetricPairAveraging n k a ha i j hij
  refine ⟨b, Or.inr ⟨i, j, hij, hmin, hmax, hlt, rfl⟩, hb, hsum, he, ?_⟩
  change (∑ t, (b t - c) ^ 2) ≤ (1 - 1 / (2 * (n : ℝ))) * (∑ t, (a t - c) ^ 2)
  have hcmin : a i ≤ c := by
    apply (le_div_iff₀ hnR).2
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun t _ => hmin t)
  have hcmax : c ≤ a j := by
    apply (div_le_iff₀ hnR).2
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun t _ => hmax t)
  have hsq (t : Fin n) : (a t - c) ^ 2 ≤ (a j - a i) ^ 2 := by
    have h1 : 0 ≤ (a j - a i) - (a t - c) := by linarith [hmax t]
    have h2 : 0 ≤ (a j - a i) + (a t - c) := by linarith [hmin t]
    nlinarith [mul_nonneg h1 h2]
  have hV : (∑ t, (a t - c) ^ 2) ≤ (n : ℝ) * (a j - a i) ^ 2 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun t _ => hsq t
  have hdiv : (∑ t, (a t - c) ^ 2) / (2 * (n : ℝ)) ≤ (a i - a j) ^ 2 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
    nlinarith
  rw [hvar c]
  calc
    _ ≤ (∑ t, (a t - c) ^ 2) - (∑ t, (a t - c) ^ 2) / (2 * (n : ℝ)) :=
      sub_le_sub_left hdiv _
    _ = _ := by ring
