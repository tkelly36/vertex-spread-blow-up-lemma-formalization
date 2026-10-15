import Tablet.RegularPair
import Tablet.FilteredProductRowCount
import Tablet.OrderedTwoPathCount
import Tablet.BalancedDegreeVarianceBound
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Operations

-- [TABLET NODE: DegreeCodegreeRegularityCriterion]
theorem DegreeCodegreeRegularityCriterion :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (n : ℕ) (δ p η : ENNReal),
      U.card = n → W.card = n → Disjoint U W → η ≤ 1 →
      δ ≤ p → p ≤ 1 → 1 ≤ δ * n → 20 * δ ≤ η ^ 5 →
      (((W ×ˢ W).filter fun z =>
          ((U.filter fun u => G.Adj u z.1).card : ENNReal) < (p - δ) * n ∨
          ((U.filter fun u => G.Adj u z.2).card : ENNReal) < (p - δ) * n ∨
          (p + δ) ^ 2 * n <
            ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 5 * δ * n ^ 2 →
      RegularPair G U W η p := by
-- BODY
  classical
  intro V _ _ G _ U W n δ p η hn hk _ hη hδp hp hδn hhier hbad
  have hpfin : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hδfin : δ ≠ ⊤ := ne_top_of_le_ne_top hpfin hδp
  have hηfin : η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hη
  have hnNat : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    simp [this] at hδn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hδpR : δ.toReal ≤ p.toReal := ENNReal.toReal_mono hpfin hδp
  have hpR : p.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp
  have hδnR : 1 ≤ δ.toReal * (n : ℝ) := by
    simpa only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast]
      using ENNReal.toReal_mono (ENNReal.mul_ne_top hδfin (by simp)) hδn
  have hhierR : 20 * δ.toReal ≤ η.toReal ^ 5 := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
      using ENNReal.toReal_mono (ENNReal.pow_ne_top hηfin) hhier
  have hδpos : 0 < δ.toReal := by
    nlinarith only [hδnR, hnpos, ENNReal.toReal_nonneg (a := δ)]
  have hηpos : 0 < η.toReal := by
    by_contra h
    have : η.toReal = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
    rw [this] at hhierR
    norm_num at hhierR
    linarith only [hhierR, hδpos]
  let bad := (W ×ˢ W).filter fun z =>
    ((U.filter fun u => G.Adj u z.1).card : ENNReal) < (p - δ) * n ∨
    ((U.filter fun u => G.Adj u z.2).card : ENNReal) < (p - δ) * n ∨
    (p + δ) ^ 2 * n < ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal)
  have hbadR : (bad.card : ℝ) ≤ 5 * δ.toReal * (n : ℝ) ^ 2 := by
    simpa only [bad, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast, ENNReal.toReal_pow] using
      ENNReal.toReal_mono (by finiteness) hbad
  -- Each low-degree vertex contributes a full row of exceptional ordered pairs.
  let L := W.filter fun w => ((U.filter fun u => G.Adj u w).card : ENNReal) < (p - δ) * n
  have hrows : L ×ˢ W ⊆ bad := by
    intro z hz
    rcases Finset.mem_product.mp hz with ⟨hz1, hz2⟩
    rcases Finset.mem_filter.mp hz1 with ⟨hzW, hzlow⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzW, hz2⟩, Or.inl hzlow⟩
  have hLsmall : (L.card : ℝ) ≤ 5 * δ.toReal * n := by
    have hcount := Finset.card_le_card hrows
    rw [Finset.card_product, hk] at hcount
    have hcountR : (L.card : ℝ) * n ≤ (bad.card : ℝ) := by exact_mod_cast hcount
    nlinarith only [hcountR, hbadR, hnpos]
  intro U' hU' W' hW' hUlarge hWlarge
  have hUlargeR : η.toReal * (n : ℝ) < U'.card := by
    simpa only [hn, ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hUlarge
  have hWlargeR : η.toReal * (n : ℝ) < W'.card := by
    simpa only [hk, ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hWlarge
  have hqpos : (0 : ℝ) < W'.card := lt_trans (mul_pos hηpos hnpos) hWlargeR
  have hU'pos : (0 : ℝ) < U'.card := lt_trans (mul_pos hηpos hnpos) hUlargeR
  have hqn : (W'.card : ℝ) ≤ U.card := by
    have hc := Finset.card_le_card hW'
    rw [hk] at hc
    rw [hn]
    exact_mod_cast hc
  let d : V → ℝ := fun u => (W'.filter fun w => G.Adj u w).card
  let r : V → ℝ := fun w => (U.filter fun u => G.Adj u w).card
  let c : V × V → ℝ := fun z => (U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card
  have hfirstCount : (∑ u ∈ U, d u) = ∑ w ∈ W', r w := by
    simp only [d, r, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have hgoodDegree : ∀ w ∈ W' \ L, (p.toReal - δ.toReal) * (n : ℝ) ≤ r w := by
    intro w hw
    have hwlow : ¬ ((U.filter fun u => G.Adj u w).card : ENNReal) < (p - δ) * n := by
      intro h
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mpr
        ⟨hW' (Finset.mem_sdiff.mp hw).1, h⟩)
    have := ENNReal.toReal_mono (by simp) (le_of_not_gt hwlow)
    simpa only [r, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hδp hpfin,
      ENNReal.toReal_natCast] using this
  -- This signed lower bound is valid even when the cardinality surrogate is negative.
  have hfirst : ((W'.card : ℝ) - 5 * δ.toReal * n) *
      (p.toReal - δ.toReal) * n ≤ ∑ u ∈ U, d u := by
    have hnum : (W'.card : ℝ) - 5 * δ.toReal * n ≤ ((W' \ L).card : ℝ) := by
      have hc : (W'.card : ℝ) ≤ ((W' \ L).card : ℝ) + L.card := by
        exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := W') (t := L))
      linarith only [hc, hLsmall]
    rw [hfirstCount]
    calc
      _ ≤ ((W' \ L).card : ℝ) * ((p.toReal - δ.toReal) * n) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hnum
          (mul_nonneg (sub_nonneg.mpr hδpR) hnpos.le)
      _ = ∑ w ∈ W' \ L, ((p.toReal - δ.toReal) * n) := by simp
      _ ≤ ∑ w ∈ W' \ L, r w := Finset.sum_le_sum hgoodDegree
      _ ≤ ∑ w ∈ W', r w := Finset.sum_le_sum_of_subset_of_nonneg
        Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
  have hsecondCount : (∑ u ∈ U, (d u) ^ 2) = ∑ z ∈ W' ×ˢ W', c z := by
    dsimp only [d, c]
    exact_mod_cast OrderedTwoPathCount U W' G.Adj
  have hcommon : ∀ z, c z ≤ (n : ℝ) := by
    intro z
    dsimp only [c]
    exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hn)
  have hgoodCommon : ∀ z ∈ W' ×ˢ W', z ∉ bad →
      c z ≤ (p.toReal + δ.toReal) ^ 2 * n := by
    intro z hz hnot
    have hzW : z ∈ W ×ˢ W := Finset.mem_product.mpr
      ⟨hW' (Finset.mem_product.mp hz).1, hW' (Finset.mem_product.mp hz).2⟩
    have hnot' : ¬ ( ((U.filter fun u => G.Adj u z.1).card : ENNReal) < (p - δ) * n ∨
        ((U.filter fun u => G.Adj u z.2).card : ENNReal) < (p - δ) * n ∨
        (p + δ) ^ 2 * n < ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal)) := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨hzW, h⟩)
    have hle : ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal) ≤
        (p + δ) ^ 2 * n := le_of_not_gt (fun h => hnot' (Or.inr (Or.inr h)))
    have := ENNReal.toReal_mono (by finiteness) hle
    simpa only [c, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add hpfin hδfin, ENNReal.toReal_natCast] using this
  have hrestricted : (((W' ×ˢ W').filter fun z => z ∈ bad).card : ℝ) ≤
      5 * δ.toReal * (n : ℝ) ^ 2 := by
    have hc : ((W' ×ˢ W').filter fun z => z ∈ bad).card ≤ bad.card :=
      Finset.card_le_card (fun _ hz => (Finset.mem_filter.mp hz).2)
    exact (by exact_mod_cast hc :
      (((W' ×ˢ W').filter fun z => z ∈ bad).card : ℝ) ≤ bad.card).trans hbadR
  -- Diagonals are included in both the moment identity and the exceptional-pair charge.
  have hsecond : (∑ u ∈ U, (d u) ^ 2) ≤
      (n : ℝ) * (W'.card : ℝ) ^ 2 * (p.toReal + δ.toReal) ^ 2 +
        5 * δ.toReal * (n : ℝ) ^ 3 := by
    rw [hsecondCount]
    calc
      _ ≤ ∑ z ∈ W' ×ˢ W', ((p.toReal + δ.toReal) ^ 2 * n +
          if z ∈ bad then (n : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hb : z ∈ bad
        · simp only [hb, if_true]
          exact (hcommon z).trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hnpos.le))
        · simpa only [hb, if_false, add_zero] using hgoodCommon z hz hb
      _ = (W'.card : ℝ) ^ 2 * ((p.toReal + δ.toReal) ^ 2 * n) +
          (((W' ×ˢ W').filter fun z => z ∈ bad).card : ℝ) * n := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul, pow_two]
      _ ≤ (W'.card : ℝ) ^ 2 * ((p.toReal + δ.toReal) ^ 2 * n) +
          (5 * δ.toReal * (n : ℝ) ^ 2) * n :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hrestricted hnpos.le)
      _ = _ := by ring
  have hcenter : (∑ u ∈ U, (d u - p.toReal * W'.card) ^ 2) ≤
      20 * δ.toReal * (n : ℝ) ^ 3 := by
    simpa only [hn] using BalancedDegreeVarianceBound U d W'.card δ.toReal p.toReal
      hqpos.le hqn hδpos.le hδpR hpR
      (by simpa only [hn] using hfirst) (by simpa only [hn] using hsecond)
  have hcenter' : (∑ u ∈ U, (d u - p.toReal * W'.card) ^ 2) ≤
      η.toReal ^ 5 * (n : ℝ) ^ 3 :=
    hcenter.trans (mul_le_mul_of_nonneg_right hhierR (by positivity))
  have hcs : (∑ u ∈ U', (d u - p.toReal * W'.card)) ^ 2 ≤
      (U'.card : ℝ) * (∑ u ∈ U, (d u - p.toReal * W'.card) ^ 2) := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq U'
      (fun u => d u - p.toReal * W'.card) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hc
    have hs : (∑ u ∈ U', (d u - p.toReal * W'.card) ^ 2) ≤
        ∑ u ∈ U, (d u - p.toReal * W'.card) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hU' (fun _ _ _ => sq_nonneg _)
    exact hc.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hs hU'pos.le)
  have hsize : η.toReal ^ 3 * (n : ℝ) ^ 3 <
      (U'.card : ℝ) * (W'.card : ℝ) ^ 2 := by
    have hsq : (η.toReal * (n : ℝ)) ^ 2 ≤ (W'.card : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) hqpos.le).mpr hWlargeR.le
    calc
      _ = (η.toReal * n) * (η.toReal * n) ^ 2 := by ring
      _ ≤ (η.toReal * n) * (W'.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ < _ := mul_lt_mul_of_pos_right hUlargeR (sq_pos_of_pos hqpos)
  have hsumsq : (∑ u ∈ U', (d u - p.toReal * W'.card)) ^ 2 <
      (η.toReal * (U'.card : ℝ) * W'.card) ^ 2 := by
    calc
      _ ≤ _ := hcs
      _ ≤ (U'.card : ℝ) * (η.toReal ^ 5 * (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hcenter' hU'pos.le
      _ < (η.toReal * (U'.card : ℝ) * W'.card) ^ 2 := by
        have := mul_lt_mul_of_pos_left hsize
          (show 0 < η.toReal ^ 2 * (U'.card : ℝ) by positivity)
        convert this using 1 <;> ring
  have hsumbound : |∑ u ∈ U', (d u - p.toReal * W'.card)| <
      η.toReal * (U'.card : ℝ) * W'.card := by
    exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa using hsumsq)
  have hsumId : (∑ u ∈ U', (d u - p.toReal * W'.card)) =
      (∑ u ∈ U', d u) - (U'.card : ℝ) * p.toReal * W'.card := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hedgeCount : (((U' ×ˢ W').filter fun z => G.Adj z.1 z.2).card : ℝ) =
      ∑ u ∈ U', d u := by
    dsimp only [d]
    exact_mod_cast FilteredProductRowCount U' W' G.Adj
  have hdensityR : (PairDensity G U' W').toReal =
      (∑ u ∈ U', d u) / ((U'.card : ℝ) * W'.card) := by
    simp only [PairDensity, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
    exact congrArg (fun x : ℝ => x / ((U'.card : ℝ) * W'.card)) hedgeCount
  have hlowerR : p.toReal - η.toReal ≤ (PairDensity G U' W').toReal := by
    rw [hdensityR]
    apply (le_div_iff₀ (mul_pos hU'pos hqpos)).mpr
    have := (abs_lt.mp hsumbound).1
    rw [hsumId] at this
    nlinarith only [this]
  have hupperR : (PairDensity G U' W').toReal ≤ p.toReal + η.toReal := by
    rw [hdensityR]
    apply (div_le_iff₀ (mul_pos hU'pos hqpos)).mpr
    have := (abs_lt.mp hsumbound).2
    rw [hsumId] at this
    nlinarith only [this]
  have hUne : (U'.card : ENNReal) ≠ 0 := by
    exact_mod_cast (show U'.card ≠ 0 by exact_mod_cast hU'pos.ne')
  have hWne : (W'.card : ENNReal) ≠ 0 := by
    exact_mod_cast (show W'.card ≠ 0 by exact_mod_cast hqpos.ne')
  have hdensityfin : PairDensity G U' W' ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp) (mul_ne_zero hUne hWne)
  constructor
  · by_cases hηp : η ≤ p
    · apply (ENNReal.toReal_le_toReal (by finiteness) hdensityfin).mp
      simpa only [ENNReal.toReal_sub_of_le hηp hpfin] using hlowerR
    · simpa only [tsub_eq_zero_of_le (le_of_not_ge hηp)] using
        (zero_le (PairDensity G U' W'))
  · apply (ENNReal.toReal_le_toReal hdensityfin (by finiteness)).mp
    simpa only [ENNReal.toReal_add hpfin hηfin] using hupperR
