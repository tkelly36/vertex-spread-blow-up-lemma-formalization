import Tablet.BipartiteFactorNetwork
import Tablet.FiniteIntegralFlow

open scoped BigOperators
universe u

-- [TABLET NODE: BipartiteFlowSaturation]
theorem BipartiteFlowSaturation {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (k : ℕ)
    (hsize : U.card = W.card)
    (f : FiniteIntegralFlow (BipartiteFactorNetwork G U W k))
    (hvalue : (∑ w, f.amount (Sum.inl none) w) = (k * U.card : ℕ)) :
    (∀ u : U, f.amount (Sum.inl none) (Sum.inl (some u)) = (k : ℤ)) ∧
    (∀ w : W, f.amount (Sum.inr (some w)) (Sum.inr none) = (k : ℤ)) ∧
    (∀ (u : U) (w : W),
      0 ≤ f.amount (Sum.inl (some u)) (Sum.inr (some w)) ∧
      f.amount (Sum.inl (some u)) (Sum.inr (some w)) ≤ 1 ∧
      (f.amount (Sum.inl (some u)) (Sum.inr (some w)) = 1 → G.Adj u.val w.val)) ∧
    (∀ u : U, (Finset.univ.filter fun w : W =>
      f.amount (Sum.inl (some u)) (Sum.inr (some w)) = 1).card = k) ∧
    (∀ w : W, (Finset.univ.filter fun u : U =>
      f.amount (Sum.inl (some u)) (Sum.inr (some w)) = 1).card = k) := by
-- BODY
  classical
  have hzero (a b : Option U ⊕ Option W)
      (hab : (BipartiteFactorNetwork G U W k).capacity a b = 0)
      (hba : (BipartiteFactorNetwork G U W k).capacity b a = 0) :
      f.amount a b = 0 := by
    have h₁ := f.bound a b
    have h₂ := f.bound b a
    rw [hab, Nat.cast_zero] at h₁
    rw [hba, Nat.cast_zero, f.skew b a] at h₂
    omega
  have hsat {T : Type u} [Fintype T] (a : T → ℤ)
      (ha : ∀ i, a i ≤ (k : ℤ))
      (hsum : (∑ i, a i) = (k : ℤ) * Fintype.card T) :
      ∀ i, a i = (k : ℤ) := by
    have he : (∑ i, a i) = ∑ _i : T, (k : ℤ) := by
      simpa [mul_comm] using hsum
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => ha j)).mp he i
      (Finset.mem_univ i)
  have hsourceSum : (∑ u : U, f.amount (Sum.inl none) (Sum.inl (some u))) =
      (k : ℤ) * U.card := by
    simpa [Fintype.sum_sum_type, Fintype.sum_option, hzero,
      BipartiteFactorNetwork] using hvalue
  have hsource : ∀ u : U, f.amount (Sum.inl none) (Sum.inl (some u)) = (k : ℤ) := by
    apply hsat (fun u : U => f.amount (Sum.inl none) (Sum.inl (some u)))
    · intro u
      simpa [BipartiteFactorNetwork] using f.bound (Sum.inl none) (Sum.inl (some u))
    · simpa only [Fintype.card_coe] using hsourceSum
  have hleft (u : U) : (∑ v, f.amount (Sum.inl (some u)) v) = 0 :=
    f.conserve _ (by simp [BipartiteFactorNetwork]) (by simp [BipartiteFactorNetwork])
  have hright (w : W) : (∑ v, f.amount (Sum.inr (some w)) v) = 0 :=
    f.conserve _ (by simp [BipartiteFactorNetwork]) (by simp [BipartiteFactorNetwork])
  have htotal : (∑ a, ∑ b, f.amount a b) = 0 := by
    have hc : (∑ a, ∑ b, f.amount a b) = -(∑ a, ∑ b, f.amount a b) := by
      calc
        _ = ∑ b, ∑ a, f.amount a b := Finset.sum_comm
        _ = ∑ b, ∑ a, -f.amount b a := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          exact f.skew a b
        _ = _ := by simp only [Finset.sum_neg_distrib]
    omega
  have hsinkDiv : (∑ v, f.amount (Sum.inr none) v) = -((k : ℤ) * U.card) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_option] at htotal
    simp only [hleft, hright, Finset.sum_const_zero, add_zero] at htotal
    rw [hvalue] at htotal
    push_cast at htotal
    omega
  have hsinkSum : (∑ w : W, f.amount (Sum.inr (some w)) (Sum.inr none)) =
      (k : ℤ) * W.card := by
    have he : (∑ v, f.amount (Sum.inr none) v) =
        -(∑ w : W, f.amount (Sum.inr (some w)) (Sum.inr none)) := by
      simp only [Fintype.sum_sum_type, Fintype.sum_option]
      simp only [hzero, BipartiteFactorNetwork, Finset.sum_const_zero, zero_add]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      exact f.skew _ _
    rw [he] at hsinkDiv
    rw [← hsize]
    omega
  have hsink : ∀ w : W, f.amount (Sum.inr (some w)) (Sum.inr none) = (k : ℤ) := by
    apply hsat (fun w : W => f.amount (Sum.inr (some w)) (Sum.inr none))
    · intro w
      simpa [BipartiteFactorNetwork] using f.bound (Sum.inr (some w)) (Sum.inr none)
    · simpa only [Fintype.card_coe] using hsinkSum
  have hmiddle (u : U) (w : W) :
      0 ≤ f.amount (Sum.inl (some u)) (Sum.inr (some w)) ∧
      f.amount (Sum.inl (some u)) (Sum.inr (some w)) ≤ 1 ∧
      (f.amount (Sum.inl (some u)) (Sum.inr (some w)) = 1 → G.Adj u.val w.val) := by
    have hlo := f.bound (Sum.inr (some w)) (Sum.inl (some u))
    rw [f.skew] at hlo
    simp only [BipartiteFactorNetwork, Nat.cast_zero] at hlo
    have hhi := f.bound (Sum.inl (some u)) (Sum.inr (some w))
    simp only [BipartiteFactorNetwork] at hhi
    by_cases hG : G.Adj u.val w.val <;> simp only [hG, ite_true, ite_false,
      Nat.cast_one, Nat.cast_zero] at hhi
    · exact ⟨by omega, hhi, fun _ => hG⟩
    · exact ⟨by omega, by omega, fun h => by omega⟩
  have hcount {T : Type u} [Fintype T] (a : T → ℤ)
      (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hsum : (∑ i, a i) = (k : ℤ)) :
      (Finset.univ.filter fun i => a i = 1).card = k := by
    have he : (∑ i, a i) = ((Finset.univ.filter fun i => a i = 1).card : ℤ) := by
      calc
        _ = ∑ i, if a i = 1 then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs with h
          · exact h
          · have := ha i
            omega
        _ = _ := by
          simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
            Finset.sum_filter, Nat.cast_ite, Nat.cast_zero]
    exact_mod_cast he.symm.trans hsum
  refine ⟨hsource, hsink, hmiddle, ?_, ?_⟩
  · intro u
    apply hcount (fun w : W => f.amount (Sum.inl (some u)) (Sum.inr (some w)))
      (fun w => ⟨(hmiddle u w).1, (hmiddle u w).2.1⟩)
    have hc := hleft u
    simp only [Fintype.sum_sum_type, Fintype.sum_option] at hc
    simp only [hzero, BipartiteFactorNetwork, Finset.sum_const_zero, add_zero, zero_add] at hc
    rw [f.skew (Sum.inl (some u)) (Sum.inl none), hsource] at hc
    omega
  · intro w
    apply hcount (fun u : U => f.amount (Sum.inl (some u)) (Sum.inr (some w)))
      (fun u => ⟨(hmiddle u w).1, (hmiddle u w).2.1⟩)
    have hc := hright w
    simp only [Fintype.sum_sum_type, Fintype.sum_option] at hc
    simp only [hzero, BipartiteFactorNetwork, Finset.sum_const_zero, add_zero, zero_add] at hc
    rw [hsink] at hc
    have he : (∑ u : U, f.amount (Sum.inr (some w)) (Sum.inl (some u))) =
        -(∑ u : U, f.amount (Sum.inl (some u)) (Sum.inr (some w))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      exact f.skew _ _
    rw [he] at hc
    omega
