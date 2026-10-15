import Tablet.MatchingEnumeration
import Tablet.RegularInducedMatchingUpperBound
import Tablet.UniformPerfectMatching
import Tablet.FourRectangleMatchingFiberBound
import Tablet.FourRectangleFactorialCancellation
import Tablet.HypergeometricMass
import Tablet.MatchingConcentrationCorrection
import Tablet.PerfectMatchingBijectionBound
import Tablet.FourRectangleSmallOrderProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: UniformMatchingHypergeometricComparison]
theorem UniformMatchingHypergeometricComparison (d ε : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hε : 0 < ε)
    (hεsmall : ε < 1 / 16) (hεd : 2 * ε < d) :
    ∃ n₀ : ℕ, 0 < n₀ ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
      (hUW : Disjoint U W) (n : ℕ),
      n₀ ≤ n → U.card = n → W.card = n →
      SuperRegularPair G U W (ENNReal.ofReal ε) (ENNReal.ofReal d) →
      ∀ (S T : Finset V), S ⊆ U → T ⊆ W →
      ∀ (hM : Nonempty {f : U → W // PerfectMatching G U W hUW f})
        (A : Finset ℕ),
        (UniformPerfectMatching G U W hUW hM).toOuterMeasure
          {f | (Finset.univ.filter fun u : U =>
            u.1 ∈ S ∧ (f.1 u).1 ∈ T).card ∈ A} ≤
        ENNReal.ofReal (Real.exp ((n : ℝ) * MatchingConcentrationCorrection d ε) *
          ∑ x ∈ A, HypergeometricMass n S.card T.card x) := by
-- BODY
  classical
  let κ := Real.sqrt ε
  let D := d + ε + 3 * κ
  let b := d - 2 * ε
  have hκ : 0 < κ := Real.sqrt_pos.2 hε
  have hκsq : κ * κ = ε := by
    simpa only [pow_two] using Real.sq_sqrt hε.le
  have hκsmall : κ < 1 / 4 := by nlinarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hb : 0 < b := sub_pos.mpr hεd
  have htwo : (2 : ENNReal) * ENNReal.ofReal ε = ENNReal.ofReal (2 * ε) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have he : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hdE : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hd
  have hd1E : ENNReal.ofReal d ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hd1
  have hεdE : 2 * ENNReal.ofReal ε < ENNReal.ofReal d := by
    rw [htwo]
    exact (ENNReal.ofReal_lt_ofReal_iff hd).mpr hεd
  have hκsqE : ENNReal.ofReal κ * ENNReal.ofReal κ = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul hκ.le, hκsq]
  have hbE : ENNReal.ofReal d - 2 * ENNReal.ofReal ε = ENNReal.ofReal b := by
    rw [htwo, ← ENNReal.ofReal_sub d (by positivity)]
  have hDE : ENNReal.ofReal d + ENNReal.ofReal ε + 3 * ENNReal.ofReal κ =
      ENNReal.ofReal D := by
    dsimp [D]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add hd.le hε.le, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  obtain ⟨n₁, hn₁⟩ := MatchingEnumeration (ENNReal.ofReal ε) (ENNReal.ofReal d)
    he hεdE hd1E
  obtain ⟨n₂, hn₂⟩ := RegularInducedMatchingUpperBound (ENNReal.ofReal ε)
    (ENNReal.ofReal d) (ENNReal.ofReal κ) he hdE hd1E hκsqE
  refine ⟨max 1 (max n₁ n₂), by omega, ?_⟩
  intro V _ _ G _ U W hUW n hn hU hW hreg S T hS hT hM A
  letI := hM
  have hnpos : 0 < n := by omega
  have hs : S.card ≤ n := (Finset.card_le_card hS).trans_eq hU
  have ht : T.card ≤ n := (Finset.card_le_card hT).trans_eq hW
  let M := {f : U → W | PerfectMatching G U W hUW f}
  let X : (U → W) → ℕ := fun f =>
    (Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f u).1 ∈ T).card
  let K : ℕ → ℝ := fun y => if κ * (n : ℝ) ≤ (y : ℝ) then
    D ^ y * (y.factorial : ℝ) else (y.factorial : ℝ)
  have hK (y : ℕ) : 0 ≤ K y := by
    dsimp [K]
    split_ifs <;> positivity
  have htotal : b ^ n * (n.factorial : ℝ) ≤ (M.ncard : ℝ) := by
    have hh := hn₁ G U W hUW n (by omega) hU hW hreg
    rw [hbE, ← ENNReal.ofReal_pow hb.le,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (pow_nonneg hb.le n),
      ← ENNReal.ofReal_natCast] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mp hh
  have htotalpos : 0 < (M.ncard : ℝ) :=
    lt_of_lt_of_le (mul_pos (pow_pos hb n) (by exact_mod_cast Nat.factorial_pos n)) htotal
  have hrect (L R : Finset V) (hLR : Disjoint L R) (y : ℕ)
      (hL : L ⊆ U) (hR : R ⊆ W) (hLc : L.card = y) (hRc : R.card = y) :
      ({f : L → R | PerfectMatching G L R hLR f}.ncard : ℝ) ≤ K y := by
    dsimp [K]
    split_ifs with hlarge
    · have hlargeE : ENNReal.ofReal κ * n ≤ y := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hκ.le]
        exact ENNReal.ofReal_le_natCast.mpr hlarge
      have hh := hn₂ G U W L R hLR n y (by omega) hU hW hreg.1
        hL hR hLc hRc hlargeE
      rw [hDE, ← ENNReal.ofReal_pow hD.le,
        ← ENNReal.ofReal_natCast y.factorial,
        ← ENNReal.ofReal_mul (pow_nonneg hD.le y), ← ENNReal.ofReal_natCast] at hh
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
    · exact_mod_cast PerfectMatchingBijectionBound G L R hLR y hLc hRc
  -- A bijection forces the three feasibility inequalities for its intersection size.
  have hfeasible (f : U → W) (hf : PerfectMatching G U W hUW f) :
      X f ≤ S.card ∧ X f ≤ T.card ∧ T.card - X f ≤ n - S.card := by
    let F : V → V := fun u => if hu : u ∈ U then (f ⟨u, hu⟩).1 else u
    have hFu (u : U) : F u.1 = (f u).1 := by simp [F, u.2]
    have hF : Set.BijOn F (U : Set V) (W : Set V) := by
      refine Set.BijOn.mk ?_ ?_ ?_
      · intro u hu
        rw [hFu ⟨u, hu⟩]
        exact (f ⟨u, hu⟩).2
      · intro u hu v hv huv
        have heq : f ⟨u, hu⟩ = f ⟨v, hv⟩ :=
          Subtype.ext ((hFu ⟨u, hu⟩).symm.trans (huv.trans (hFu ⟨v, hv⟩)))
        exact congrArg (fun a : U => a.1) (hf.1.1 heq)
      · intro v hv
        obtain ⟨u, hu⟩ := hf.1.2 ⟨v, hv⟩
        exact ⟨u.1, u.2, (hFu u).trans (congrArg (fun b : W => b.1) hu)⟩
    have hx : (S.filter fun u => F u ∈ T).card = X f := by
      symm
      apply Finset.card_bij (fun u _ => u.1)
      · intro u hu
        obtain ⟨_, huS, huT⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨huS, (hFu u).symm ▸ huT⟩
      · intro u hu v hv huv
        exact Subtype.ext huv
      · intro v hv
        obtain ⟨hvS, hvT⟩ := Finset.mem_filter.mp hv
        refine ⟨⟨v, hS hvS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, ?_⟩, rfl⟩
        simpa only [F, dif_pos (hS hvS)] using hvT
    have hp := FourRectangleMatchingPartition U W S T F hF hS hT n (X f) hU hW hx
    have ha := Finset.mem_powersetCard.mp hp.1
    have hb' := Finset.mem_powersetCard.mp hp.2.1
    have he' := Finset.mem_powersetCard.mp hp.2.2.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [← ha.2]
      exact Finset.card_le_card ha.1
    · rw [← hb'.2]
      exact Finset.card_le_card hb'.1
    · rw [← he'.2, ← hU, ← Finset.card_sdiff_of_subset hS]
      exact Finset.card_le_card he'.1
  have hmass (x : ℕ) : 0 ≤ HypergeometricMass n S.card T.card x := by
    unfold HypergeometricMass
    split_ifs <;> positivity
  have hpoint (x : ℕ) :
      ({f : U → W | PerfectMatching G U W hUW f ∧ X f = x}.ncard : ℝ) /
        (M.ncard : ℝ) ≤
      Real.exp ((n : ℝ) * MatchingConcentrationCorrection d ε) *
        HypergeometricMass n S.card T.card x := by
    by_cases hx : x ≤ S.card ∧ x ≤ T.card ∧ T.card - x ≤ n - S.card
    · let y : Fin 4 → ℕ := ![x, S.card - x, T.card - x, n - S.card - (T.card - x)]
      have hy : ∑ i, y i = n := by
        rw [Fin.sum_univ_four]
        dsimp [y]
        omega
      have hp := FourRectangleSmallOrderProduct κ D n y hκ hκsmall hD hnpos hy
      rw [Fin.prod_univ_four, Fin.prod_univ_four] at hp
      change K x * K (S.card - x) * K (T.card - x) *
        K (n - S.card - (T.card - x)) ≤
        D ^ n * Real.exp (-3 * κ * (n : ℝ) * Real.log (min D 1)) *
          ((x.factorial : ℝ) * ((S.card - x).factorial : ℝ) *
            ((T.card - x).factorial : ℝ) * ((n - S.card - (T.card - x)).factorial : ℝ)) at hp
      let C : ℝ := (S.card.choose x : ℝ) * (T.card.choose x : ℝ) *
        ((n - T.card).choose (S.card - x) : ℝ) *
        ((n - S.card).choose (T.card - x) : ℝ)
      let F : ℝ := (x.factorial : ℝ) * ((S.card - x).factorial : ℝ) *
        ((T.card - x).factorial : ℝ) * ((n - S.card - (T.card - x)).factorial : ℝ)
      let E := Real.exp (-3 * κ * (n : ℝ) * Real.log (min D 1))
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hF : 0 < F := by dsimp [F]; positivity
      have hfiber := FourRectangleMatchingFiberBound G U W S T hUW n x hU hW
        hS hT hx.1 hx.2.1 hx.2.2 K (fun z _ => hK z) hrect
      have hnum :
          ({f : U → W | PerfectMatching G U W hUW f ∧ X f = x}.ncard : ℝ) ≤
          C * (D ^ n * E * F) :=
        hfiber.trans (mul_le_mul_of_nonneg_left hp hC)
      have hcoef : D ^ n * E / b ^ n =
          Real.exp ((n : ℝ) * MatchingConcentrationCorrection d ε) := by
        have hpw : (D / b) ^ n = Real.exp ((n : ℝ) * Real.log (D / b)) := by
          rw [Real.exp_nat_mul, Real.exp_log (div_pos hD hb)]
        calc
          D ^ n * E / b ^ n = (D / b) ^ n * E := by rw [div_pow]; ring
          _ = Real.exp ((n : ℝ) * Real.log (D / b) +
              (-3 * κ * (n : ℝ) * Real.log (min D 1))) := by
            rw [hpw, ← Real.exp_add]
          _ = _ := by
            congr 1
            dsimp [MatchingConcentrationCorrection, D, b, κ]
            ring
      have hcancel : C * F / (n.factorial : ℝ) =
          HypergeometricMass n S.card T.card x := by
        rw [HypergeometricMass, if_pos hx.1]
        exact FourRectangleFactorialCancellation n S.card T.card x hs ht
          hx.1 hx.2.1 hx.2.2
      calc
        _ ≤ C * (D ^ n * E * F) / (b ^ n * (n.factorial : ℝ)) :=
          div_le_div₀ (by positivity) hnum (by positivity) htotal
        _ = (D ^ n * E / b ^ n) * (C * F / (n.factorial : ℝ)) := by ring
        _ = _ := by rw [hcoef, hcancel]
    · have hempty : {f : U → W | PerfectMatching G U W hUW f ∧ X f = x} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro f ⟨hf, hfx⟩
        exact hx (hfx ▸ hfeasible f hf)
      have hzero : HypergeometricMass n S.card T.card x = 0 := by
        unfold HypergeometricMass
        by_cases hxs : x ≤ S.card
        · rw [if_pos hxs]
          by_cases hxt : x ≤ T.card
          · have hbad : n - T.card < S.card - x := by omega
            rw [Nat.choose_eq_zero_of_lt hbad, Nat.cast_zero, mul_zero, zero_div]
          · rw [Nat.choose_eq_zero_of_lt (not_le.mp hxt), Nat.cast_zero, zero_mul, zero_div]
        · rw [if_neg hxs]
      rw [hempty, Set.ncard_empty, Nat.cast_zero, zero_div, hzero, mul_zero]
  change (PMF.uniformOfFintype {f : U → W // PerfectMatching G U W hUW f}).toOuterMeasure
    {f | X f.1 ∈ A} ≤ _
  have hevent :
      (PMF.uniformOfFintype {f : U → W // PerfectMatching G U W hUW f}).toOuterMeasure
        {f | X f.1 ∈ A} =
      ENNReal.ofReal (∑ x ∈ A,
        ({f : {f : U → W // PerfectMatching G U W hUW f} | X f.1 = x}.ncard : ℝ) /
          (Fintype.card {f : U → W // PerfectMatching G U W hUW f} : ℝ)) := by
    have hc : Fintype.card
        ({f : {f : U → W // PerfectMatching G U W hUW f} | X f.1 ∈ A} : Set _) =
        ∑ x ∈ A,
          {f : {f : U → W // PerfectMatching G U W hUW f} | X f.1 = x}.ncard := by
      simp only [Fintype.card_subtype, Set.ncard_eq_toFinset_card']
      simpa using (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset {f : U → W // PerfectMatching G U W hUW f})
        A (fun f => X f.1)).symm
    rw [PMF.toOuterMeasure_uniformOfFintype_apply, hc]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_div_of_pos (by
        exact_mod_cast Fintype.card_pos
          (α := {f : U → W // PerfectMatching G U W hUW f}))]
    congr 1
    rw [Nat.cast_sum, Finset.sum_div]
  rw [hevent]
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_nonneg _)
    (Finset.sum_nonneg fun x _ => hmass x))).mpr
  have hc : Fintype.card {f : U → W // PerfectMatching G U W hUW f} = M.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq M
  have hfib (x : ℕ) :
      {f : {f : U → W // PerfectMatching G U W hUW f} | X f.1 = x}.ncard =
        {f : U → W | PerfectMatching G U W hUW f ∧ X f = x}.ncard := by
    calc
      _ = ({f : U → W | X f = x} ∩
          {f : U → W | PerfectMatching G U W hUW f}).ncard :=
        Set.ncard_subtype (fun f : U → W => PerfectMatching G U W hUW f)
          {f : U → W | X f = x}
      _ = _ := by
        congr 1
        ext f
        exact and_comm
  simp only [hc, hfib]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => hpoint x
