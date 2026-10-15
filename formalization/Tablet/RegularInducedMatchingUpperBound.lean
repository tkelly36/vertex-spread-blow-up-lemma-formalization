import Tablet.RegularPair
import Tablet.PerfectMatching
import Tablet.PerfectMatchingBijectionBound
import Tablet.BregmanMatchingDegreeProduct
import Tablet.RegularPairUpperTail
import Tablet.FactorialRootExceptionalProduct
import EntropyMethodsFormalization.BregmanMinc
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

open scoped BigOperators ENNReal

-- [TABLET NODE: RegularInducedMatchingUpperBound]
theorem RegularInducedMatchingUpperBound :
    ∀ ε d κ : ENNReal, 0 < ε → 0 < d → d ≤ 1 → κ * κ = ε →
      ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (U W S T : Finset V) (hST : Disjoint S T) (n y : ℕ),
        n₀ ≤ n → U.card = n → W.card = n →
        RegularPair G U W ε d → S ⊆ U → T ⊆ W →
        S.card = y → T.card = y → κ * n ≤ y →
        ({f : S → T | PerfectMatching G S T hST f}.ncard : ENNReal) ≤
          (d + ε + 3 * κ) ^ y * (y.factorial : ENNReal) := by
-- BODY
  intro ε d κ hε hd hd1 hκ
  classical
  by_cases hc : 1 ≤ d + ε + 3 * κ
  · refine ⟨0, ?_⟩
    intro V _ _ G _ U W S T hST n y hn hU hW hreg hS hT hSc hTc hy
    have hcount : ({f : S → T | PerfectMatching G S T hST f}.ncard : ENNReal) ≤
        (y.factorial : ENNReal) := by
      exact_mod_cast PerfectMatchingBijectionBound G S T hST y hSc hTc
    exact hcount.trans (by
      simpa only [one_mul] using
        mul_le_mul_right' (one_le_pow₀ hc) (y.factorial : ENNReal))
  have hc : d + ε + 3 * κ < 1 := lt_of_not_ge hc
  have hcf : d + ε + 3 * κ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hc.le
  obtain ⟨hDf, h3f⟩ := ENNReal.add_ne_top.mp hcf
  obtain ⟨hdf, hεf⟩ := ENNReal.add_ne_top.mp hDf
  have hκf : κ ≠ ∞ := (ENNReal.lt_top_of_mul_ne_top_right h3f (by norm_num)).ne
  have hκ0 : κ ≠ 0 := by
    intro hz
    have : ε = 0 := by simpa [hz] using hκ.symm
    exact hε.ne' this
  have hκR : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκf
  have hDR : 0 < d.toReal + ε.toReal :=
    add_pos_of_pos_of_nonneg (ENNReal.toReal_pos hd.ne' hdf) ENNReal.toReal_nonneg
  have hctoReal : (d + ε + 3 * κ).toReal = d.toReal + ε.toReal + 3 * κ.toReal := by
    rw [ENNReal.toReal_add hDf h3f, ENNReal.toReal_add hdf hεf, ENNReal.toReal_mul]
    norm_num
  have hcR : d.toReal + ε.toReal + 3 * κ.toReal < 1 := by
    have h := (ENNReal.toReal_lt_toReal hcf ENNReal.one_ne_top).2 hc
    simpa only [hctoReal, ENNReal.toReal_one] using h
  have heqR : κ.toReal * κ.toReal = ε.toReal := by
    simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal hκ
  have hκthird : κ.toReal < 1 / 3 := by
    have := ENNReal.toReal_nonneg (a := d)
    have := ENNReal.toReal_nonneg (a := ε)
    linarith
  have hεR : ε.toReal < κ.toReal := by nlinarith
  have hε1 : ε ≤ 1 := by
    apply (ENNReal.toReal_le_toReal hεf ENNReal.one_ne_top).1
    simp only [ENNReal.toReal_one]
    linarith
  obtain ⟨y₀, hy₀, hprod⟩ :=
    FactorialRootExceptionalProduct (d.toReal + ε.toReal) κ.toReal hDR hκR hcR
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((y₀ : ℝ) / κ.toReal + 1)
  have hn₀pos : 0 < n₀ := by
    have : 0 < (n₀ : ℝ) := lt_trans (by positivity) hn₀
    exact_mod_cast this
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ U W S T hST n y hn hU hW hreg hS hT hSc hTc hy
  have hnpos : 0 < n := hn₀pos.trans_le hn
  have hyR : κ.toReal * (n : ℝ) ≤ (y : ℝ) := by
    have h := ENNReal.toReal_mono (by simp) hy
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using h
  have hlarge : y₀ ≤ y := by
    have hnR : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hdiv : (y₀ : ℝ) / κ.toReal < (n : ℝ) := by linarith
    have hm : (y₀ : ℝ) < κ.toReal * (n : ℝ) := by
      have := (div_lt_iff₀ hκR).mp hdiv
      simpa only [mul_comm] using this
    exact_mod_cast (hm.trans_le hyR).le
  let eS : S ≃ Fin y := Fintype.equivFinOfCardEq (by simpa using hSc)
  let eT : T ≃ Fin y := Fintype.equivFinOfCardEq (by simpa using hTc)
  let r : Fin y → ℕ := fun i => (T.filter fun w => G.Adj (eS.symm i) w).card
  obtain ⟨hzero, hbound⟩ := BregmanMatchingDegreeProduct G S T hST eS eT
  by_cases hz : ∃ i, r i = 0
  · have hm := hzero hz
    simp only [hm, Nat.cast_zero]
    exact bot_le
  have hp : ∀ i, 0 < r i := by
    intro i
    exact Nat.pos_of_ne_zero (fun hi => hz ⟨i, hi⟩)
  have hr : ∀ i, r i ≤ y := by
    intro i
    exact (Finset.card_filter_le _ _).trans_eq hTc
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hTlarge : ε * W.card < (T.card : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hεf (by simp)) (by simp)).1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hW, hTc]
    exact (mul_lt_mul_of_pos_right hεR hnR).trans_le hyR
  have htail := RegularPairUpperTail G U W T ε d hε1 hd1 hreg hT hTlarge
  let P : V → Prop := fun v =>
    (d.toReal + ε.toReal + κ.toReal) * (y : ℝ) <
      ((T.filter fun w => G.Adj v w).card : ℝ)
  let A := S.filter P
  let B := U.filter fun v => (d + ε) * T.card <
    ((T.filter fun w => G.Adj v w).card : ENNReal)
  have hindex : ((Finset.univ : Finset (Fin y)).filter
      (fun i => P (eS.symm i))).card = A.card := by
    have hs : (∑ i : Fin y, if P (eS.symm i) then (1 : ℕ) else 0) = A.card := by
      calc
        _ = ∑ v : S, if P v then (1 : ℕ) else 0 := eS.symm.sum_comp _
        _ = _ := by
          rw [Finset.sum_coe_sort S (fun v : V => if P v then (1 : ℕ) else 0),
            Finset.sum_boole]
          simp [A]
    simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hs
  have hAB : A ⊆ B := by
    intro v hv
    obtain ⟨hvS, hvP⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hS hvS, ?_⟩
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top hDf (by simp)) (by simp)).1
    simp only [ENNReal.toReal_mul, ENNReal.toReal_add hdf hεf,
      ENNReal.toReal_natCast, hTc]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right ENNReal.toReal_nonneg) (Nat.cast_nonneg y)) hvP
  have hAreal : (A.card : ℝ) ≤ ε.toReal * (n : ℝ) := by
    have hcards : (A.card : ENNReal) ≤ (B.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hAB
    have hAENN : (A.card : ENNReal) ≤ ε * U.card :=
      hcards.trans htail
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hεf (by simp)) hAENN
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hU] using h
  have hexc : (((Finset.univ : Finset (Fin y)).filter fun i =>
      (d.toReal + ε.toReal + κ.toReal) * (y : ℝ) < (r i : ℝ)).card : ℝ) ≤
      κ.toReal * (y : ℝ) := by
    change (((Finset.univ : Finset (Fin y)).filter
      (fun i => P (eS.symm i))).card : ℝ) ≤ _
    rw [hindex]
    calc
      (A.card : ℝ) ≤ ε.toReal * (n : ℝ) := hAreal
      _ = κ.toReal * (κ.toReal * (n : ℝ)) := by rw [← heqR, mul_assoc]
      _ ≤ κ.toReal * (y : ℝ) := mul_le_mul_of_nonneg_left hyR hκR.le
  have hreal : ({f : S → T | PerfectMatching G S T hST f}.ncard : ℝ) ≤
      (d.toReal + ε.toReal + 3 * κ.toReal) ^ y * (y.factorial : ℝ) :=
    (hbound hp).trans (hprod y hlarge r hp hr hexc)
  have hENN := ENNReal.ofReal_le_ofReal hreal
  have hcoef : ENNReal.ofReal (d.toReal + ε.toReal + 3 * κ.toReal) =
      d + ε + 3 * κ := by
    rw [← hctoReal, ENNReal.ofReal_toReal hcf]
  have hnonneg : 0 ≤ d.toReal + ε.toReal + 3 * κ.toReal := by positivity
  simpa only [ENNReal.ofReal_mul (pow_nonneg hnonneg y),
    ENNReal.ofReal_pow hnonneg, ENNReal.ofReal_natCast, hcoef] using hENN
