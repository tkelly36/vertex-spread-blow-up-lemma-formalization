import Tablet.BipartiteRegularFactorCriterion
import Tablet.SuperRegularPair
import Tablet.RestrictedRowEdgeLowerBound

-- [TABLET NODE: SuperRegularSpanningFactor]
theorem SuperRegularSpanningFactor :
    ∀ ε d : ENNReal, 0 < ε → 2 * ε < d → d ≤ 1 →
      ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
        (hUW : Disjoint U W) (n : ℕ), n₀ ≤ n → U.card = n → W.card = n →
        SuperRegularPair G U W ε d →
        ∃ (k : ℕ) (F : SimpleGraph V), F ≤ G ∧
          (d - 2 * ε) * (n : ENNReal) ≤ (k : ENNReal) ∧
          (∀ u ∈ U, {w | w ∈ W ∧ F.Adj u w}.ncard = k) ∧
          (∀ w ∈ W, {u | u ∈ U ∧ F.Adj u w}.ncard = k) := by
-- BODY
  classical
  intro ε d hε hεd hd
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hd
  have hεtwo : ε ≤ 2 * ε := by
    simpa only [one_mul] using
      (mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2) ε)
  have hεtop : ε ≠ ⊤ := (hεtwo.trans_lt hεd).ne_top
  have hεle : ε ≤ d := (hεtwo.trans_lt hεd).le
  let e : ℝ := ε.toReal
  let δ : ℝ := d.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  have hed : 2 * e < δ := by
    have h := (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by norm_num) hεtop) hdtop).mpr hεd
    simpa [ENNReal.toReal_mul, e, δ] using h
  have hsub : (d - ε).toReal = δ - e :=
    ENNReal.toReal_sub_of_le hεle hdtop
  have hsubtwo : (d - 2 * ε).toReal = δ - 2 * e := by
    rw [ENNReal.toReal_sub_of_le hεd.le hdtop, ENNReal.toReal_mul]
    simp [e, δ]
  refine ⟨Nat.ceil (2 / e), ?_⟩
  intro V _ _ G _ U W hUW n hn hU hW hsr
  have hlarge : 2 ≤ e * (n : ℝ) := by
    have hnreal : 2 / e ≤ (n : ℝ) :=
      (Nat.le_ceil (2 / e)).trans (by exact_mod_cast hn)
    simpa only [mul_comm] using (div_le_iff₀ he).mp hnreal
  have hnpos : 0 < (n : ℝ) := by nlinarith
  let k := Nat.ceil ((δ - 2 * e) * (n : ℝ))
  let D : ℝ := (δ - e) * (n : ℝ)
  have hklo : (δ - 2 * e) * (n : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ D := by
    have h := Nat.ceil_lt_add_one
      (mul_nonneg (by linarith : 0 ≤ δ - 2 * e) hnpos.le)
    change (k : ℝ) < (δ - 2 * e) * (n : ℝ) + 1 at h
    dsimp only [D]
    nlinarith
  have hsmallD : e * (n : ℝ) < D := by
    dsimp only [D]
    nlinarith
  have hdegreeU : ∀ u ∈ U,
      D ≤ ((W.filter fun w => G.Adj u w).card : ℝ) := by
    intro u hu
    have h := (hsr.2.1 u hu).1
    rw [hW] at h
    have hr := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top hdtop tsub_le_self) (by simp))
      (by simp)).mpr h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hsub] using hr
  have hdegreeW : ∀ w ∈ W,
      D ≤ ((U.filter fun u => G.Adj w u).card : ℝ) := by
    intro w hw
    have h := (hsr.2.2 w hw).1
    rw [hU] at h
    have hr := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top hdtop tsub_le_self) (by simp))
      (by simp)).mpr h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hsub,
      G.adj_comm] using hr
  -- This affine estimate handles either small side of a positive-deficit cut.
  have hsmall : ∀ a b C : ℝ, 0 ≤ a → b ≤ n → (n : ℝ) < a + b →
      a ≤ e * n → a * (D - ((n : ℝ) - b)) ≤ C →
      (k : ℝ) * (a + b - n) ≤ C := by
    intro a b C ha hb hab hasmall hrow
    let t : ℝ := n - b
    have ht : 0 ≤ t := sub_nonneg.mpr hb
    have hta : t < a := by dsimp only [t]; linarith
    have haD : a ≤ D := hasmall.trans hsmallD.le
    have hdef : a + b - n = a - t := by dsimp only [t]; ring
    rw [hdef]
    change a * (D - t) ≤ C at hrow
    by_cases hak : a ≤ (k : ℝ)
    · have h₁ := mul_nonneg ha (sub_nonneg.mpr hkhi)
      have h₂ := mul_nonneg ht (sub_nonneg.mpr hak)
      nlinarith
    · have h₁ := mul_nonneg ha (sub_nonneg.mpr haD)
      have h₂ := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hak))
        (sub_nonneg.mpr hta.le)
      nlinarith
  have hcuts : ∀ A ⊆ U, ∀ B ⊆ W,
      k * (A.card + B.card - U.card) ≤
        ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card := by
    intro A hAU B hBW
    rw [hU]
    by_cases hdef : A.card + B.card ≤ n
    · simp only [Nat.sub_eq_zero_of_le hdef, mul_zero, Nat.zero_le]
    have hdefpos : n < A.card + B.card := lt_of_not_ge hdef
    have hab : (n : ℝ) < (A.card : ℝ) + B.card := by exact_mod_cast hdefpos
    have hAn : (A.card : ℝ) ≤ n := by
      exact_mod_cast (hU ▸ Finset.card_le_card hAU)
    have hBn : (B.card : ℝ) ≤ n := by
      exact_mod_cast (hW ▸ Finset.card_le_card hBW)
    have hreal : (k : ℝ) * ((A.card : ℝ) + B.card - n) ≤
        (((A.product B).filter fun p => G.Adj p.1 p.2).card : ℝ) := by
      by_cases hAsmall : (A.card : ℝ) ≤ e * n
      · apply hsmall A.card B.card _ (Nat.cast_nonneg _) hBn hab hAsmall
        have h := RestrictedRowEdgeLowerBound A W B G.Adj D hBW
          (fun u hu => hdegreeU u (hAU hu))
        simpa only [hW] using h
      by_cases hBsmall : (B.card : ℝ) ≤ e * n
      · have hrow := RestrictedRowEdgeLowerBound B U A G.Adj D hAU
          (fun w hw => hdegreeW w (hBW hw))
        have hswap : ((B.product A).filter fun p => G.Adj p.1 p.2).card =
            ((A.product B).filter fun p => G.Adj p.1 p.2).card := by
          rw [FilteredProductRowCount B A G.Adj, FilteredProductRowCount A B G.Adj]
          simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro w hw
          simp only [G.adj_comm]
        rw [hswap, hU] at hrow
        have h := hsmall B.card A.card _ (Nat.cast_nonneg _) hAn
          (by linarith) hBsmall hrow
        simpa only [add_comm] using h
      have hAgt : ε * (U.card : ENNReal) < (A.card : ENNReal) := by
        apply (ENNReal.toReal_lt_toReal
          (ENNReal.mul_ne_top hεtop (by simp)) (by simp)).mp
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hU] using
          (lt_of_not_ge hAsmall)
      have hBgt : ε * (W.card : ENNReal) < (B.card : ENNReal) := by
        apply (ENNReal.toReal_lt_toReal
          (ENNReal.mul_ne_top hεtop (by simp)) (by simp)).mp
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hW] using
          (lt_of_not_ge hBsmall)
      have hAzero : (A.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hAgt)
      have hBzero : (B.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hBgt)
      have hdensity := (hsr.1 A hAU B hBW hAgt hBgt).1
      unfold PairDensity at hdensity
      have hedge := (ENNReal.le_div_iff_mul_le
        (Or.inl (mul_ne_zero hAzero hBzero))
        (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))).mp hdensity
      have hedgeReal : (δ - e) * ((A.card : ℝ) * B.card) ≤
          (((A.product B).filter fun p => G.Adj p.1 p.2).card : ℝ) := by
        have h := (ENNReal.toReal_le_toReal
          (ENNReal.mul_ne_top (ne_top_of_le_ne_top hdtop tsub_le_self)
            (ENNReal.mul_ne_top (by simp) (by simp))) (by simp)).mpr hedge
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hsub] using h
      have hproduct : (n : ℝ) * ((A.card : ℝ) + B.card - n) ≤
          (A.card : ℝ) * B.card := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hAn) (sub_nonneg.mpr hBn)]
      calc
        (k : ℝ) * ((A.card : ℝ) + B.card - n) ≤
            D * ((A.card : ℝ) + B.card - n) :=
          mul_le_mul_of_nonneg_right hkhi (by linarith)
        _ = (δ - e) * ((n : ℝ) * ((A.card : ℝ) + B.card - n)) := by
          dsimp only [D]; ring
        _ ≤ (δ - e) * ((A.card : ℝ) * B.card) :=
          mul_le_mul_of_nonneg_left hproduct (by linarith)
        _ ≤ _ := hedgeReal
    have hcast : ((k * (A.card + B.card - n) : ℕ) : ℝ) =
        (k : ℝ) * ((A.card : ℝ) + B.card - n) := by
      rw [Nat.cast_mul, Nat.cast_sub hdefpos.le, Nat.cast_add]
    have hnatReal : ((k * (A.card + B.card - n) : ℕ) : ℝ) ≤
        (((A.product B).filter fun p => G.Adj p.1 p.2).card : ℝ) := by
      rw [hcast]
      exact hreal
    exact_mod_cast hnatReal
  obtain ⟨F, hFG, hFU, hFW⟩ :=
    (BipartiteRegularFactorCriterion G U W hUW k (hU.trans hW.symm)).mpr hcuts
  refine ⟨k, F, hFG, ?_, hFU, hFW⟩
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (ne_top_of_le_ne_top hdtop tsub_le_self) (by simp))
    (by simp)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hsubtwo] using hklo
