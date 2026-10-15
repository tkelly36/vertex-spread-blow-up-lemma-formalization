import Tablet.MatchingEnumeration
import Tablet.UniformPerfectMatching
import Tablet.CylinderEvent
import Tablet.BijectionCompletionCount
import Mathlib.Analysis.SpecialFunctions.Exp

-- [TABLET NODE: MatchingManyEdges]
theorem MatchingManyEdges :
    ∀ ε d : ENNReal, 0 < ε → 2 * ε < d → d ≤ 1 →
      ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V]
        [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (U W : Finset V) (hUW : Disjoint U W) (n : ℕ),
        n₀ ≤ n → U.card = n → W.card = n → SuperRegularPair G U W ε d →
        ∀ (h : Nonempty {f : U → W // PerfectMatching G U W hUW f})
          (s : ℕ) (x : Fin s → U) (y : Fin s → W), Function.Injective x →
          ((UniformPerfectMatching G U W hUW h).map Subtype.val).toOuterMeasure
              (CylinderEvent x y) ≤ C ^ n / (n : ENNReal) ^ s := by
-- BODY
  classical
  intro ε d hε hεd hd
  obtain ⟨n₁, hn₁⟩ := MatchingEnumeration ε d hε hεd hd
  let b := d - 2 * ε
  have hb : 0 < b := tsub_pos_iff_lt.mpr hεd
  have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((tsub_le_self : d - 2 * ε ≤ d).trans hd)
  have hbR : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop
  let c : ℝ := Real.exp 1 / b.toReal
  have hc : 1 ≤ c := by
    have hb1 : b.toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        ((tsub_le_self : d - 2 * ε ≤ d).trans hd)
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    dsimp [c]
    exact (le_div_iff₀ hbR).mpr (by nlinarith)
  refine ⟨ENNReal.ofReal c, ?_, ENNReal.ofReal_ne_top, max n₁ 1, ?_⟩
  · simpa using ENNReal.ofReal_le_ofReal hc
  intro V _ _ G _ U W hUW n hn hU hW hreg h s x y hx
  letI := h
  have hnpos : 0 < n := by omega
  have hs : s ≤ n := by
    have hh := Fintype.card_le_of_injective x hx
    simpa only [Fintype.card_fin, Fintype.card_coe, hU] using hh
  let M := {f : U → W | PerfectMatching G U W hUW f}
  letI : Nonempty M := h
  let E := {f : U → W | PerfectMatching G U W hUW f ∧ ∀ i, f (x i) = y i}
  have hnum : E.ncard ≤ (n - s).factorial := by
    have hsubset : E ⊆
        {f : U → W | Function.Bijective f ∧ ∀ i, f (x i) = y i} := by
      intro f hf
      exact ⟨hf.1.1, hf.2⟩
    exact (Set.ncard_mono hsubset).trans
      (BijectionCompletionCount n s (by simpa using hU) (by simpa using hW) x y hx)
  have hden : b ^ n * (n.factorial : ENNReal) ≤ (M.ncard : ENNReal) :=
    hn₁ G U W hUW n (by omega) hU hW hreg
  have hprob :
      ((UniformPerfectMatching G U W hUW h).map Subtype.val).toOuterMeasure
        (CylinderEvent x y) = (E.ncard : ENNReal) / (M.ncard : ENNReal) := by
    rw [PMF.toOuterMeasure_map_apply]
    change (PMF.uniformOfFintype M).toOuterMeasure
      {f | ∀ i, f.1 (x i) = y i} = _
    rw [PMF.uniformOfFintype]
    trans ((Finset.univ.filter fun f : M => ∀ i, f.1 (x i) = y i).card : ENNReal) /
      (Fintype.card M : ENNReal)
    · convert PMF.toOuterMeasure_uniformOfFinset_apply Finset.univ_nonempty
        {f : M | ∀ i, f.1 (x i) = y i} using 1
      congr 2
      apply congrArg Finset.card
      ext f
      simp
    have htotal : Fintype.card M = M.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    have hevent : (Finset.univ.filter fun f : M =>
        ∀ i, f.1 (x i) = y i).card = E.ncard := by
      calc
        _ = {f : M | ∀ i, f.1 (x i) = y i}.ncard := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
          rfl
        _ = ({f : U → W | ∀ i, f (x i) = y i} ∩ M).ncard :=
          Set.ncard_subtype (fun f : U → W => PerfectMatching G U W hUW f)
            {f : U → W | ∀ i, f (x i) = y i}
        _ = E.ncard := by
          congr 1
          ext f
          exact and_comm
    rw [htotal, hevent]
  rw [hprob]
  by_cases hs0 : s = 0
  · subst s
    have he : E = M := by
      ext f
      simp [E, M]
    have hm : M.ncard ≠ 0 := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      exact ne_of_gt Fintype.card_pos
    rw [he, ENNReal.div_self (by exact_mod_cast hm) (ENNReal.natCast_ne_top _)]
    simp only [pow_zero, div_one]
    exact one_le_pow₀ (by simpa using ENNReal.ofReal_le_ofReal hc)
  have hratio : (E.ncard : ENNReal) / (M.ncard : ENNReal) ≤
      ((n - s).factorial : ENNReal) / (b ^ n * (n.factorial : ENNReal)) := by
    exact ENNReal.div_le_div (by exact_mod_cast hnum) hden
  apply hratio.trans
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hsmall : ((n - s).factorial : ℝ) ≤ (n : ℝ) ^ (n - s) := by
    exact_mod_cast (Nat.factorial_le_pow (n - s)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n s) (n - s))
  have hexp : (n : ℝ) ^ n ≤ Real.exp 1 ^ n * (n.factorial : ℝ) := by
    have hh := Real.pow_div_factorial_le_exp (n : ℝ) hnR.le n
    rw [div_le_iff₀ hfac] at hh
    have heq : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simpa using Real.exp_nat_mul 1 n
    rwa [heq] at hh
  have hprod : ((n - s).factorial : ℝ) * (n : ℝ) ^ s ≤
      Real.exp 1 ^ n * (n.factorial : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (n - s) * (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (n : ℝ) ^ n := by rw [← pow_add, Nat.sub_add_cancel hs]
      _ ≤ _ := hexp
  have hreal : ((n - s).factorial : ℝ) /
      (b.toReal ^ n * (n.factorial : ℝ)) ≤ c ^ n / (n : ℝ) ^ s := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    dsimp [c]
    rw [div_pow, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (pow_pos hbR n))]
    exact hprod
  have hbcoe : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbtop
  have hcnonneg : 0 ≤ c := le_trans (by norm_num) hc
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hbR.le,
    ENNReal.ofReal_pow hcnonneg, ENNReal.ofReal_pow hnR.le,
    hbcoe, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast] at hh
  exact hh
