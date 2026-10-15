import Tablet.NearEqualRegularTriplet
import Tablet.MatchingInducedGraph
import Tablet.UniformPerfectMatching
import Tablet.MatchingEnumeration
import Tablet.UniformMatchingSetImageConcentration
import Tablet.NearEqualRegularPairGoodCodegrees
import Tablet.NearEqualDegreeCodegreeRegularityCriterion
import Tablet.SuperRegularPair
import Tablet.NearEqualFourGraphsParameters
import Tablet.MatchingInducedDegreeConcentration
import Tablet.MatchingInducedCodegreeConcentration
import Tablet.MatchingInducedSuperRegularCertificate
import Tablet.FourGraphsPolynomialLossAbsorption

-- [TABLET NODE: NearEqualFourGraphs]
theorem NearEqualFourGraphs :
    ∀ d₁₂ d₁₃ d₂₃ : ENNReal,
      0 < d₁₂ → d₁₂ ≤ 1 → 0 < d₁₃ → d₁₃ ≤ 1 →
      0 < d₂₃ → d₂₃ ≤ 1 →
      ∃ ε'₀ : ENNReal, 0 < ε'₀ ∧ ∀ ε' : ENNReal, 0 < ε' → ε' ≤ ε'₀ →
      ∃ ε₀ : ENNReal, 0 < ε₀ ∧ ∀ ε : ENNReal, 0 < ε → ε ≤ ε₀ →
        ∃ a₀ : ENNReal, 0 < a₀ ∧ ∀ a : ENNReal, 0 < a → a ≤ a₀ →
          ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
            (F₁₂ F₁₃ F₂₃ : SimpleGraph V)
            [DecidableRel F₁₂.Adj] [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
            (W₁ W₂ W₃ : Finset V) (m : ℕ),
            n₀ ≤ m →
            NearEqualRegularTriplet F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ m ε d₁₂ d₁₃ d₂₃ →
            ∀ (h₁₂ : Disjoint W₁ W₂)
              (hM : Nonempty {σ : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ σ}),
              let μ := UniformPerfectMatching F₁₂ W₁ W₂ h₁₂ hM
              let L : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inl
              let R : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inr
              1 - (1 - a) ^ m ≤
                μ.toOuterMeasure {σ |
                  letI : DecidableRel
                      (MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ σ).Adj :=
                    Classical.decRel _
                  SuperRegularPair
                    (MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ σ)
                    L R ε' (d₁₃ * d₂₃)} := by
-- BODY
  classical
  intro d₁₂ d₁₃ d₂₃ hd₁₂ hd₁₂1 hd₁₃ hd₁₃1 hd₂₃ hd₂₃1
  refine ⟨1, by norm_num, ?_⟩
  intro η hη hη1
  obtain ⟨δ, ζ, e, hδ, hδp, hδη, hhier, hζ, he, he1, hwindows⟩ :=
    NearEqualFourGraphsParameters d₁₂ d₁₃ d₂₃ η
      hd₁₂ hd₁₂1 hd₁₃ hd₁₃1 hd₂₃ hd₂₃1 hη hη1
  have hx : 0 < d₁₃ / 2 := ENNReal.div_pos hd₁₃.ne' (by norm_num)
  have hy : 0 < d₂₃ / 2 := ENNReal.div_pos hd₂₃.ne' (by norm_num)
  have hx1 : d₁₃ / 2 ≤ 1 := by
    calc
      d₁₃ / 2 ≤ 1 / 2 := by gcongr
      _ ≤ 1 := by norm_num
  have hy1 : d₂₃ / 2 ≤ 1 := by
    calc
      d₂₃ / 2 ≤ 1 / 2 := by gcongr
      _ ≤ 1 := by norm_num
  have hx21 : (d₁₃ / 2) ^ 2 ≤ 1 := by simpa using pow_le_pow_left' hx1 2
  have hy21 : (d₂₃ / 2) ^ 2 ≤ 1 := by simpa using pow_le_pow_left' hy1 2
  obtain ⟨θD, hθD, hdegree⟩ := UniformMatchingSetImageConcentration
    d₁₂ (d₁₃ / 2) (d₂₃ / 2) ζ hd₁₂ hd₁₂1 hx hx1 hy hy1 hζ
  obtain ⟨θC, hθC, hcommon⟩ := UniformMatchingSetImageConcentration
    d₁₂ ((d₁₃ / 2) ^ 2) ((d₂₃ / 2) ^ 2) ζ
      hd₁₂ hd₁₂1 (ENNReal.pow_pos hx 2) hx21 (ENNReal.pow_pos hy 2) hy21 hζ
  refine ⟨min e (min θD θC), lt_min he (lt_min hθD hθC), ?_⟩
  intro ε hε hεsmall
  have hεe : ε ≤ e := hεsmall.trans (min_le_left _ _)
  have hεD : ε ≤ θD := hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε ≤ θC := hεsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hεδ, hεη, hεd, hεx, hεy, hS, hT, hS₂, hT₂, hlo, hhi, hpoly⟩ :=
    hwindows ε hεe
  obtain ⟨cD, hcD, ND, hdegree⟩ := hdegree ε hε hεD
  obtain ⟨cC, hcC, NC, hcommon⟩ := hcommon ε hε hεC
  let c := max cD cC
  have hc : c < 1 := max_lt hcD hcC
  obtain ⟨a₀, ha₀, habsorb⟩ := FourGraphsPolynomialLossAbsorption c hc
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha haa
  obtain ⟨NA, hNA, hAbs⟩ := habsorb a ha haa
  have hp : d₁₃ * d₂₃ ≤ 1 := by simpa using mul_le_mul' hd₁₃1 hd₂₃1
  have hδfin : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hδp.trans hp)
  have hδR : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδfin
  obtain ⟨Nδ, hNδ⟩ := exists_nat_ge (1 / δ.toReal)
  refine ⟨max NA (max Nδ (max ND NC)), ?_⟩
  intro V _ _ F₁₂ F₁₃ F₂₃ _ _ _ W₁ W₂ W₃ m hm ht h₁₂ hM
  let μ := UniformPerfectMatching F₁₂ W₁ W₂ h₁₂ hM
  let L : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inl
  let R : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inr
  have htrip := ht
  obtain ⟨hW₁, hW₂, hk, _, _, _, hreg, hF, hH, _⟩ := ht
  have hmA : NA ≤ m := (le_max_left _ _).trans hm
  have hmδ : Nδ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmD : ND ≤ m := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hmC : NC ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hm2 : 2 ≤ m := hNA.trans hmA
  have hmpos : 0 < m := by omega
  have hδm : 1 ≤ δ * (m : ENNReal) := by
    apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top
      (ENNReal.mul_ne_top hδfin (by simp))).mp
    have hN : 1 / δ.toReal ≤ (m : ℝ) := hNδ.trans (by exact_mod_cast hmδ)
    simpa only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      mul_comm] using (div_le_iff₀ hδR).mp hN
  have hconcD (S T : Finset V) (hSU : S ⊆ W₁) (hTW : T ⊆ W₂)
      (hs : d₁₃ / 2 * m ≤ S.card) (ht : d₂₃ / 2 * m ≤ T.card) :=
    (tsub_le_tsub_left (pow_le_pow_left' (le_max_left cD cC) m) 1).trans
      (hdegree F₁₂ W₁ W₂ h₁₂ m hmD hW₁ hW₂ hreg S T hSU hTW hs ht hM)
  have hconcC (S T : Finset V) (hSU : S ⊆ W₁) (hTW : T ⊆ W₂)
      (hs : (d₁₃ / 2) ^ 2 * m ≤ S.card) (ht : (d₂₃ / 2) ^ 2 * m ≤ T.card) :=
    (tsub_le_tsub_left (pow_le_pow_left' (le_max_right cD cC) m) 1).trans
      (hcommon F₁₂ W₁ W₂ h₁₂ m hmC hW₁ hW₂ hreg S T hSU hTW hs ht hM)
  let D : Set {f : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ f} := {f |
    let A := MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ f.1
    letI : DecidableRel A.Adj := Classical.decRel _
    ∀ z : W₃,
      (d₁₃ * d₂₃ - δ) * m ≤ ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ∧
      ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ≤ (d₁₃ * d₂₃ + δ) * m}
  let C : Set {f : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ f} := {f |
    let A := MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ f.1
    letI : DecidableRel A.Adj := Classical.decRel _
    (((R ×ˢ R).filter fun z => (d₁₃ * d₂₃ + δ) ^ 2 * m <
      ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 6 * ε * (W₃.card : ENNReal) ^ 2}
  have hD : 1 - (W₃.card : ENNReal) * c ^ m ≤ μ.toOuterMeasure D :=
    MatchingInducedDegreeConcentration F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ h₁₂ m
      ε d₁₃ d₂₃ δ ζ c μ hmpos hW₁ hW₂ hF hH hS hT hlo hhi hconcD
  have hbadF := NearEqualRegularPairGoodCodegrees F₁₃ W₁ W₃ m ε d₁₃
    hW₁ hk hm2 hεx hF
  have hbadH := NearEqualRegularPairGoodCodegrees F₂₃ W₂ W₃ m ε d₂₃
    hW₂ hk hm2 hεy hH
  have hC : 1 - (W₃.card : ENNReal) ^ 2 * c ^ m ≤ μ.toOuterMeasure C :=
    MatchingInducedCodegreeConcentration F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ h₁₂ m
      ε d₁₃ d₂₃ δ ζ c μ hmpos hW₁ hW₂ hS₂ hT₂ hpoly hbadF hbadH hconcC
  have htotal (E : Set {f : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ f}) :
      μ.toOuterMeasure E + μ.toOuterMeasure Eᶜ = 1 := by
    as_aux_lemma =>
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ f, μ f := by
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : f ∈ E <;> simp [Set.indicator, hf]
      _ = 1 := by simpa only [tsum_fintype] using μ.tsum_coe
  have hcomp (E : Set {f : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ f})
      (b : ENNReal) (h : 1 - b ≤ μ.toOuterMeasure E) : μ.toOuterMeasure Eᶜ ≤ b := by
    have hle : μ.toOuterMeasure E ≤ 1 := by
      rw [← htotal E]
      exact le_self_add
    apply ENNReal.le_of_add_le_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
    rw [htotal E]
    exact tsub_le_iff_right.mp h
  have hfailure : μ.toOuterMeasure (D ∩ C)ᶜ ≤
      (((m + 1 : ℕ) : ENNReal) + ((m + 1 : ℕ) : ENNReal) ^ 2) * c ^ m := by
    calc
      _ ≤ μ.toOuterMeasure Dᶜ + μ.toOuterMeasure Cᶜ := by
        rw [Set.compl_inter]
        exact MeasureTheory.measure_union_le _ _
      _ ≤ (W₃.card : ENNReal) * c ^ m + (W₃.card : ENNReal) ^ 2 * c ^ m :=
        add_le_add (hcomp D _ hD) (hcomp C _ hC)
      _ = ((W₃.card : ENNReal) + (W₃.card : ENNReal) ^ 2) * c ^ m := by rw [add_mul]
      _ ≤ _ := by
        have hkupper : W₃.card ≤ m + 1 := by rcases hk with hk | hk | hk <;> omega
        have hkE : (W₃.card : ENNReal) ≤ ((m + 1 : ℕ) : ENNReal) := by exact_mod_cast hkupper
        gcongr
  have hsuccess :
      1 - ((((m + 1 : ℕ) : ENNReal) + ((m + 1 : ℕ) : ENNReal) ^ 2) * c ^ m) ≤
        μ.toOuterMeasure (D ∩ C) := by
    apply tsub_le_iff_right.mpr
    rw [← htotal (D ∩ C)]
    exact add_le_add le_rfl hfailure
  apply (tsub_le_tsub_left (hAbs m hmA) 1).trans (hsuccess.trans _)
  apply MeasureTheory.measure_mono
  intro f hf
  exact MatchingInducedSuperRegularCertificate F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ m
    ε d₁₂ d₁₃ d₂₃ δ η h₁₂ htrip f.1 f.2 hm2 hεη hεδ hδη hδp hp hη1 hδm hhier
      hf.1 hf.2
