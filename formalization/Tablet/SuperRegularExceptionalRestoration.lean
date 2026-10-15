import Tablet.SuperRegularPair
import Tablet.PairDensityReal
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.Order.Floor.Ring
import Tablet.ExceptionalCoreEdgeExtension
import Tablet.ExceptionalRectangleDensity

-- [TABLET NODE: SuperRegularExceptionalRestoration]
theorem SuperRegularExceptionalRestoration
    {V : Type*} [Fintype V] [DecidableEq V]
    (H F : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel F.Adj]
    (U W U₀ W₀ : Finset V) (n : ℕ) (c h η : ℝ)
    (hU : U.card = n) (hW : W.card = n) (hUW : Disjoint U W)
    (hcover : U ∪ W = Finset.univ)
    (hbip : ∀ ⦃u v⦄, H.Adj u v →
      (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U))
    (hU₀ : U₀ ⊆ U) (hW₀ : W₀ ⊆ W)
    (hc : 0 < c) (hc1 : c < 1) (hh : 0 < h)
    (hhc : h ≤ c / 100) (hη : 0 < η) (hη1 : η < 1)
    (h3 : 3 * h < η) (h4 : 4 * h < η)
    (hbudget : 2 * h + 4 * h / η < η) (hfloor : 1 ≤ h * (n : ℝ))
    (hbadU : ((U \ U₀).card : ℝ) ≤ 2 * h * n)
    (hbadW : ((W \ W₀).card : ℝ) ≤ 2 * h * n)
    (hreserveU : ∀ u ∈ U, (7 * c / 4) * n ≤
      ((W.filter fun w => H.Adj u w).card : ℝ))
    (hreserveW : ∀ w ∈ W, (7 * c / 4) * n ≤
      ((U.filter fun u => H.Adj u w).card : ℝ))
    (hFH : F ≤ H)
    (hFsupport : ∀ ⦃u v⦄, F.Adj u v →
      (u ∈ U₀ ∧ v ∈ W₀) ∨ (u ∈ W₀ ∧ v ∈ U₀))
    (hdegU : ∀ u ∈ U₀, (c - 4 * h) * n ≤
      ((W₀.filter fun w => F.Adj u w).card : ℝ) ∧
      ((W₀.filter fun w => F.Adj u w).card : ℝ) ≤ (c + 2 * h) * n)
    (hdegW : ∀ w ∈ W₀, (c - 4 * h) * n ≤
      ((U₀.filter fun u => F.Adj u w).card : ℝ) ∧
      ((U₀.filter fun u => F.Adj u w).card : ℝ) ≤ (c + 2 * h) * n)
    (hrect : ∀ A ⊆ U₀, ∀ B ⊆ W₀, h * n < (A.card : ℝ) →
      h * n < (B.card : ℝ) → |(F.edgeDensity A B : ℝ) - c| ≤ 2 * h) :
    ∃ G' : SimpleGraph V, ∃ _ : DecidableRel G'.Adj,
      G' ≤ H ∧ SuperRegularPair G' U W (ENNReal.ofReal η) (ENNReal.ofReal c) := by
-- BODY
  classical
  have hnR : (0 : ℝ) < n := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (by positivity)
    rw [hn0, mul_zero] at hfloor
    norm_num at hfloor
  have hn : 0 < n := by exact_mod_cast hnR
  let k := Nat.floor (c * n)
  have hkhi : (k : ℝ) ≤ c * n := Nat.floor_le (by positivity)
  have hklo : c * n - 1 ≤ (k : ℝ) := by
    have hk := Nat.lt_floor_add_one (c * (n : ℝ))
    linarith only [hk]
  -- Removing the opposite exceptional part leaves enough reserve for k edges.
  have hreserve : ∀ (A A₀ : Finset V) (v : V),
      ((A \ A₀).card : ℝ) ≤ 2 * h * n →
      (7 * c / 4) * n ≤ ((A.filter fun w => H.Adj v w).card : ℝ) →
      k ≤ (A₀.filter fun w => H.Adj v w).card := by
    intro A A₀ v hbad hres
    have hsub : A.filter (fun w => H.Adj v w) ⊆
        (A₀.filter fun w => H.Adj v w) ∪ (A \ A₀) := by
      intro w hw
      obtain ⟨hwA, hadj⟩ := Finset.mem_filter.mp hw
      by_cases hw0 : w ∈ A₀
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw0, hadj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwA, hw0⟩)
    have hcount : ((A.filter fun w => H.Adj v w).card : ℝ) ≤
        (A₀.filter fun w => H.Adj v w).card + (A \ A₀).card := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hmargin : 0 ≤ (3 * c / 4 - 2 * h) * (n : ℝ) := by
      apply mul_nonneg _ hnR.le
      linarith only [hc, hhc]
    have hreal : (k : ℝ) ≤ (A₀.filter fun w => H.Adj v w).card := by
      nlinarith only [hkhi, hres, hbad, hcount, hmargin]
    exact_mod_cast hreal
  have hNU : ∀ u ∈ U \ U₀, k ≤ (W₀.filter fun w => H.Adj u w).card := by
    intro u hu
    exact hreserve W W₀ u hbadW (hreserveU u (Finset.mem_sdiff.mp hu).1)
  have hNW : ∀ w ∈ W \ W₀, k ≤ (U₀.filter fun u => H.Adj w u).card := by
    intro w hw
    apply hreserve U U₀ w hbadU
    have he : U.filter (fun u => H.Adj w u) = U.filter (fun u => H.Adj u w) := by
      apply Finset.filter_congr
      intro u _
      exact H.adj_comm w u
    rw [he]
    exact hreserveW w (Finset.mem_sdiff.mp hw).1
  obtain ⟨G, hGdec, hGH, _, hagree, hexU, hexW, hcoreU, hcoreW⟩ :=
    ExceptionalCoreEdgeExtension H F U W U₀ W₀ k hUW hU₀ hW₀ hFH
      hFsupport hNU hNW
  letI := hGdec
  -- The same degree calculation applies to each of the two parts.
  have hdegrees : ∀ (A A₀ B B₀ : Finset V),
      ((B \ B₀).card : ℝ) ≤ 2 * h * n →
      (∀ v ∈ A₀, (c - 4 * h) * n ≤
        ((B₀.filter fun w => F.Adj v w).card : ℝ) ∧
        ((B₀.filter fun w => F.Adj v w).card : ℝ) ≤ (c + 2 * h) * n) →
      (∀ v ∈ A \ A₀, (B.filter fun w => G.Adj v w).card = k) →
      (∀ v ∈ A₀,
        (B₀.filter fun w => F.Adj v w).card ≤ (B.filter fun w => G.Adj v w).card ∧
        (B.filter fun w => G.Adj v w).card ≤
          (B₀.filter fun w => F.Adj v w).card + (B \ B₀).card) →
      ∀ v ∈ A, (c - η) * n ≤ ((B.filter fun w => G.Adj v w).card : ℝ) ∧
        ((B.filter fun w => G.Adj v w).card : ℝ) ≤ (c + η) * n := by
    intro A A₀ B B₀ hbad hdeg hex hcore v hv
    by_cases hv0 : v ∈ A₀
    · obtain ⟨hfl, hfu⟩ := hdeg v hv0
      obtain ⟨hgl, hgu⟩ := hcore v hv0
      have hglR : ((B₀.filter fun w => F.Adj v w).card : ℝ) ≤
          (B.filter fun w => G.Adj v w).card := by exact_mod_cast hgl
      have hguR : ((B.filter fun w => G.Adj v w).card : ℝ) ≤
          (B₀.filter fun w => F.Adj v w).card + (B \ B₀).card := by exact_mod_cast hgu
      have hm := mul_nonneg (sub_nonneg.mpr h4.le) hnR.le
      constructor <;> nlinarith only [hfl, hfu, hglR, hguR, hbad, hm]
    · rw [hex v (Finset.mem_sdiff.mpr ⟨hv, hv0⟩)]
      have hm := mul_nonneg (show 0 ≤ η - h by linarith only [h4, hh]) hnR.le
      have hp := mul_nonneg hη.le hnR.le
      constructor <;> nlinarith only [hklo, hkhi, hfloor, hm, hp]
  have hdegUR := hdegrees U U₀ W W₀ hbadW hdegU hexU hcoreU
  have hdegWR : ∀ w ∈ W, (c - η) * n ≤
      ((U.filter fun u => G.Adj w u).card : ℝ) ∧
      ((U.filter fun u => G.Adj w u).card : ℝ) ≤ (c + η) * n := by
    apply hdegrees W W₀ U U₀ hbadU _ hexW hcoreW
    intro w hw
    have he : U₀.filter (fun u => F.Adj w u) = U₀.filter (fun u => F.Adj u w) := by
      apply Finset.filter_congr
      intro u _
      exact F.adj_comm w u
    rw [he]
    exact hdegW w hw
  have hdensity := ExceptionalRectangleDensity F G U W U₀ W₀ n c h η
    hc hc1 hh hhc hη h3 hbudget hn hbadU hbadW hagree hrect
  -- Truncated subtraction is converted only when its real endpoint is nonnegative.
  have hconvert : ∀ (m : ℕ) (z : ENNReal), z ≠ ⊤ →
      (c - η) * m ≤ z.toReal → z.toReal ≤ (c + η) * m →
      (ENNReal.ofReal c - ENNReal.ofReal η) * m ≤ z ∧
        z ≤ (ENNReal.ofReal c + ENNReal.ofReal η) * m := by
    intro m z hz hl hu
    constructor
    · by_cases hηc : η ≤ c
      · rw [← ENNReal.ofReal_sub c hη.le]
        apply (ENNReal.toReal_le_toReal (by finiteness) hz).mp
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hηc),
          ENNReal.toReal_natCast] using hl
      · have he : ENNReal.ofReal c - ENNReal.ofReal η = 0 :=
          tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal (le_of_not_ge hηc))
        rw [he, zero_mul]
        exact zero_le z
    · rw [← ENNReal.ofReal_add hc.le hη.le]
      apply (ENNReal.toReal_le_toReal hz (by finiteness)).mp
      simpa only [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (add_nonneg hc.le hη.le),
        ENNReal.toReal_natCast] using hu
  refine ⟨G, hGdec, hGH, ?_, ?_, ?_⟩
  · intro X hXU Y hYW hXen hYen
    have hX : η * n < (X.card : ℝ) := by
      have hr := (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hXen
      simpa only [hU, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
        ENNReal.toReal_natCast] using hr
    have hY : η * n < (Y.card : ℝ) := by
      have hr := (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mpr hYen
      simpa only [hW, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
        ENNReal.toReal_natCast] using hr
    have hxne : X.Nonempty := Finset.card_pos.mp (by
      have hr := lt_trans (mul_pos hη hnR) hX
      exact_mod_cast hr)
    have hyne : Y.Nonempty := Finset.card_pos.mp (by
      have hr := lt_trans (mul_pos hη hnR) hY
      exact_mod_cast hr)
    obtain ⟨hfin, hd, _⟩ := PairDensityReal G X Y hxne hyne
    obtain ⟨hl, hu⟩ := abs_lt.mp (hdensity X hXU Y hYW hX hY)
    have hconv := hconvert 1 (PairDensity G X Y) hfin
      (by rw [hd]; simp only [Nat.cast_one, mul_one]; linarith only [hl])
      (by rw [hd]; simp only [Nat.cast_one, mul_one]; linarith only [hu])
    simpa only [Nat.cast_one, mul_one] using hconv
  · intro u hu
    obtain ⟨hl, hr⟩ := hdegUR u hu
    rw [hW]
    exact hconvert n ((W.filter fun w => G.Adj u w).card : ENNReal) (by simp)
      (by simpa only [ENNReal.toReal_natCast] using hl)
      (by simpa only [ENNReal.toReal_natCast] using hr)
  · intro w hw
    obtain ⟨hl, hr⟩ := hdegWR w hw
    rw [hU]
    have he : U.filter (fun u => G.Adj u w) = U.filter (fun u => G.Adj w u) := by
      apply Finset.filter_congr
      intro u _
      exact G.adj_comm u w
    rw [he]
    exact hconvert n ((U.filter fun u => G.Adj w u).card : ENNReal) (by simp)
      (by simpa only [ENNReal.toReal_natCast] using hl)
      (by simpa only [ENNReal.toReal_natCast] using hr)
