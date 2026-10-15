import Tablet.MatchingEnumeration
import Tablet.RegularInducedMatchingUpperBound
import Tablet.UniformPerfectMatching
import Tablet.UniformMatchingHypergeometricComparison
import Tablet.HypergeometricTwoTail
import Tablet.MatchingConcentrationCorrectionAbsorption

-- [TABLET NODE: UniformMatchingSetImageConcentration]
theorem UniformMatchingSetImageConcentration :
    ∀ d α β η : ENNReal,
      0 < d → d ≤ 1 → 0 < α → α ≤ 1 →
      0 < β → β ≤ 1 → 0 < η →
      ∃ ε₀ : ENNReal, 0 < ε₀ ∧ ∀ ε : ENNReal, 0 < ε → ε ≤ ε₀ →
      ∃ c : ENNReal, c < 1 ∧ ∃ n₀ : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
        (hUW : Disjoint U W) (n : ℕ),
        n₀ ≤ n → U.card = n → W.card = n →
        SuperRegularPair G U W ε d →
        ∀ (S T : Finset V), S ⊆ U → T ⊆ W →
        α * n ≤ S.card → β * n ≤ T.card →
        ∀ (hM : Nonempty {f : U → W // PerfectMatching G U W hUW f}),
          let μ := UniformPerfectMatching G U W hUW hM
          μ.toOuterMeasure {f |
              ((S.card : ENNReal) * T.card / n - η * n ≤
                ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal)) ∧
              (((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ≤
                (S.card : ENNReal) * T.card / n + η * n)} ≥ 1 - c ^ n := by
-- BODY
  intro d α β η hd hd1 hα hα1 hβ hβ1 hη
  classical
  by_cases hηtop : η = ⊤
  · subst η
    refine ⟨1, by norm_num, ?_⟩
    intro ε hε hε₀
    refine ⟨0, by norm_num, 1, ?_⟩
    intro V _ _ G _ U W hUW n hn hU hW hreg S T hS hT hs ht hM
    have hn0 : (n : ENNReal) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    simp only [ENNReal.top_mul hn0, ENNReal.sub_top, zero_le, add_top, le_top,
      and_self, Set.setOf_true]
    rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
    exact tsub_le_self
  · have hdtop : d ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hd1 (by simp))
    have hdr : 0 < d.toReal := ENNReal.toReal_pos hd.ne' hdtop
    have hd1r : d.toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hd1
    have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
    let γ : ℝ := η.toReal ^ 2 / (4 * (1 + η.toReal / 3))
    have hγ : 0 < γ := by
      dsimp [γ]
      positivity
    obtain ⟨ε₀, hε₀, hsmall, hdsmall, nAbs, hnAbs, habs⟩ :=
      (MatchingConcentrationCorrectionAbsorption d.toReal hdr hd1r).2 γ hγ
    refine ⟨ENNReal.ofReal ε₀, ENNReal.ofReal_pos.mpr hε₀, ?_⟩
    intro ε hε hεle
    have hεtop : ε ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hεle ENNReal.ofReal_lt_top)
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hεler : ε.toReal ≤ ε₀ := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hεle
      simpa [ENNReal.toReal_ofReal hε₀.le] using this
    have hεsmall : ε.toReal < 1 / 16 := lt_of_le_of_lt hεler hsmall
    have hεd : 2 * ε.toReal < d.toReal := by linarith
    obtain ⟨nCount, hnCount, hcompare⟩ :=
      UniformMatchingHypergeometricComparison d.toReal ε.toReal hdr hd1r
        hεr hεsmall hεd
    refine ⟨ENNReal.ofReal (Real.exp (-γ / 2)), ?_, max nAbs nCount, ?_⟩
    · exact (ENNReal.ofReal_lt_one).2 (Real.exp_lt_one_iff.mpr (by linarith))
    · intro V _ _ G _ U W hUW n hn hU hW hreg S T hS hT hs ht hM
      have hpmfComplements (p : PMF {f : U → W // PerfectMatching G U W hUW f})
          (B : Set {f : U → W // PerfectMatching G U W hUW f}) :
          p.toOuterMeasure B + p.toOuterMeasure Bᶜ = 1 := by
        as_aux_lemma =>
        rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
          ← Finset.sum_add_distrib]
        calc
          _ = ∑ f, p f := by
            apply Finset.sum_congr rfl
            intro f _
            by_cases hf : f ∈ B <;> simp [Set.indicator, hf]
          _ = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      have hnAbs' : nAbs ≤ n := le_trans (le_max_left _ _) hn
      have hnCount' : nCount ≤ n := le_trans (le_max_right _ _) hn
      have hnpos : 0 < n := lt_of_lt_of_le hnAbs hnAbs'
      have hsle : S.card ≤ n := hU ▸ Finset.card_le_card hS
      have htle : T.card ≤ n := hW ▸ Finset.card_le_card hT
      let A := (Finset.range (n + 1)).filter (fun x : ℕ =>
        η.toReal * n < |(x : ℝ) - (S.card : ℝ) * T.card / n|)
      have hcount := hcompare G U W hUW n hnCount' hU hW
        (by simpa only [ENNReal.ofReal_toReal hdtop, ENNReal.ofReal_toReal hεtop]
          using hreg) S T hS hT hM A
      have htail := HypergeometricTwoTail n S.card T.card hnpos hsle htle η.toReal hηr
      have hcorrection := (habs ε.toReal hεr hεler).2 n hnAbs'
      have hdecay :
          Real.exp ((n : ℝ) * MatchingConcentrationCorrection d.toReal ε.toReal) *
            (∑ x ∈ A, HypergeometricMass n S.card T.card x) ≤
          Real.exp (-γ / 2) ^ n := by
        calc
          _ ≤ Real.exp ((n : ℝ) * MatchingConcentrationCorrection d.toReal ε.toReal) *
              (2 * Real.exp (-(η.toReal ^ 2 / (2 * (1 + η.toReal / 3))) * n)) :=
            mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
          _ = 2 * Real.exp ((n : ℝ) *
              (MatchingConcentrationCorrection d.toReal ε.toReal - 2 * γ)) := by
            rw [← mul_assoc, mul_comm (Real.exp _) 2, mul_assoc, ← Real.exp_add]
            congr 2
            dsimp [γ]
            field_simp
            ring
          _ ≤ _ := hcorrection
      have hfailure := hcount.trans (ENNReal.ofReal_le_ofReal hdecay)
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le] at hfailure
      have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hnpos.ne'
      have hmfin : (S.card : ENNReal) * T.card / n ≠ ⊤ :=
        ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hn0
      have hηnfin : η * (n : ENNReal) ≠ ⊤ :=
        ENNReal.mul_ne_top hηtop (by simp)
      -- Truncated subtraction is removed before converting the finite interval.
      have hinterval (x : ℕ) :
          (((S.card : ENNReal) * T.card / n - η * n ≤ (x : ENNReal)) ∧
            ((x : ENNReal) ≤ (S.card : ENNReal) * T.card / n + η * n)) ↔
          |(x : ℝ) - (S.card : ℝ) * T.card / n| ≤ η.toReal * n := by
        as_aux_lemma =>
        have hxfin : (x : ENNReal) ≠ ⊤ := by simp
        rw [tsub_le_iff_right,
          ← ENNReal.toReal_le_toReal hmfin (ENNReal.add_ne_top.mpr ⟨hxfin, hηnfin⟩),
          ← ENNReal.toReal_le_toReal hxfin (ENNReal.add_ne_top.mpr ⟨hmfin, hηnfin⟩)]
        simp only [ENNReal.toReal_add hxfin hηnfin, ENNReal.toReal_add hmfin hηnfin,
          ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
        rw [abs_le]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
      let μ := UniformPerfectMatching G U W hUW hM
      let E : Set {f : U → W // PerfectMatching G U W hUW f} := {f |
        (((S.card : ENNReal) * T.card / n - η * n ≤
          ((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal)) ∧
        (((Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card : ENNReal) ≤
          (S.card : ENNReal) * T.card / n + η * n))}
      have hbad : {f : {f : U → W // PerfectMatching G U W hUW f} |
          (Finset.univ.filter fun u : U => u.1 ∈ S ∧ (f.1 u).1 ∈ T).card ∈ A} = Eᶜ := by
        ext f
        have hXle : (Finset.univ.filter fun u : U =>
            u.1 ∈ S ∧ (f.1 u).1 ∈ T).card ≤ n := by
          calc
            _ ≤ (Finset.univ : Finset U).card := Finset.card_filter_le _ _
            _ = n := by simpa using hU
        simp only [A, E, Set.mem_setOf_eq, Set.mem_compl_iff,
          Finset.mem_filter, Finset.mem_range, hinterval, not_le]
        exact and_iff_right (Nat.lt_succ_of_le hXle)
      rw [hbad] at hfailure
      have htotal := hpmfComplements μ E
      change 1 - ENNReal.ofReal (Real.exp (-γ / 2)) ^ n ≤ μ.toOuterMeasure E
      apply tsub_le_iff_right.mpr
      rw [← htotal]
      exact add_le_add le_rfl hfailure
