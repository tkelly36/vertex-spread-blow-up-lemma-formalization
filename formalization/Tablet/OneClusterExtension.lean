import Tablet.NearEqualFourGraphs
import Tablet.NearEqualRegularTriplet
import Tablet.UniformPerfectMatchingSpread
import Tablet.VertexSpreadConditioning

-- [TABLET NODE: OneClusterExtension]
theorem OneClusterExtension :
    ∀ {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
      (F₁₂ : SimpleGraph V) [DecidableRel F₁₂.Adj]
      (F₁₃ F₂₃ : ι → SimpleGraph V)
      [∀ k, DecidableRel (F₁₃ k).Adj] [∀ k, DecidableRel (F₂₃ k).Adj]
      (W₁ W₂ : Finset V) (W₃ : ι → Finset V) (n Δ : ℕ)
      (ε₁₂ d₁₂ : ENNReal) (εIn εOut d₁₃ d₂₃ : ι → ENNReal)
      (a C : ENNReal),
      Fintype.card ι ≤ Δ →
      Δ * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹ →
      0 < ε₁₂ → 4 * ε₁₂ < d₁₂ → d₁₂ ≤ 1 →
      C / n ≤ 1 →
      W₁.card = n → W₂.card = n →
      SuperRegularPair F₁₂ W₁ W₂ ε₁₂ d₁₂ →
      (∀ k, NearEqualRegularTriplet F₁₂ (F₁₃ k) (F₂₃ k)
        W₁ W₂ (W₃ k) n (εIn k) d₁₂ (d₁₃ k) (d₂₃ k)) →
      ∀ (h₁₂ : Disjoint W₁ W₂)
        (hM : Nonempty {σ : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ σ}),
        let μ₀ := UniformPerfectMatching F₁₂ W₁ W₂ h₁₂ hM
        let μ := μ₀.map Subtype.val
        VertexSpreadOn μ (C / (2 * n)) Set.univ →
        (∀ k,
          1 - (1 - a) ^ n ≤ μ₀.toOuterMeasure {σ |
            letI : DecidableRel
                (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ).Adj :=
              Classical.decRel _
            let L : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inl
            let R : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inr
            SuperRegularPair
              (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ)
              L R (εOut k) (d₁₃ k * d₂₃ k)}) →
        ∃ E : Set (W₁ → W₂),
          (∀ σ, σ ∈ E ↔ ∀ k,
            letI : DecidableRel
                (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ).Adj :=
              Classical.decRel _
            let L : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inl
            let R : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inr
            SuperRegularPair
              (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ)
              L R (εOut k) (d₁₃ k * d₂₃ k)) ∧
          (2 : ENNReal)⁻¹ ≤ μ.toOuterMeasure E ∧
          ∃ hE : ∃ σ ∈ E, σ ∈ μ.support,
            VertexSpreadOn (μ.filter E hE) (C / n) Set.univ := by
-- BODY
  classical
  intro ι V _ _ _ _ F₁₂ _ F₁₃ F₂₃ _ _ W₁ W₂ W₃ n Δ
    ε₁₂ d₁₂ εIn εOut d₁₃ d₂₃ a C hcard hloss _ _ _ hC _ _ _ _ h₁₂ hM
  dsimp only
  intro hspread hgood
  let μ₀ := UniformPerfectMatching F₁₂ W₁ W₂ h₁₂ hM
  let μ := μ₀.map Subtype.val
  let G : ι → Set (W₁ → W₂) := fun k => {σ |
    letI : DecidableRel
        (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ).Adj :=
      Classical.decRel _
    let L : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inl
    let R : Finset (W₁ ⊕ W₃ k) := Finset.univ.image Sum.inr
    SuperRegularPair
      (MatchingInducedGraph (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) σ)
      L R (εOut k) (d₁₃ k * d₂₃ k)}
  let E : Set (W₁ → W₂) := ⋂ k, G k
  have hmap (k : ι) : 1 - (1 - a) ^ n ≤ μ.toOuterMeasure (G k) := by
    rw [PMF.toOuterMeasure_map_apply]
    exact hgood k
  have hcompl (S : Set (W₁ → W₂)) :
      μ.toOuterMeasure Sᶜ = 1 - μ.toOuterMeasure S := by
    have hsum : μ.toOuterMeasure S + μ.toOuterMeasure Sᶜ = 1 := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
      calc
        (∑' σ, (S.indicator μ σ + (Sᶜ).indicator μ σ)) = (∑' σ, μ σ) := by
          apply tsum_congr
          intro σ
          by_cases hσ : σ ∈ S <;> simp [hσ]
        _ = 1 := μ.tsum_coe
    exact (ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top hsum.symm).symm
  have hpow : (1 - a) ^ n ≤ 1 :=
    pow_le_one₀ (zero_le _) tsub_le_self
  have hfail (k : ι) : μ.toOuterMeasure (G k)ᶜ ≤ (1 - a) ^ n := by
    rw [hcompl]
    calc
      1 - μ.toOuterMeasure (G k) ≤ 1 - (1 - (1 - a) ^ n) :=
        tsub_le_tsub_left (hmap k) 1
      _ = (1 - a) ^ n := ENNReal.sub_sub_cancel ENNReal.one_ne_top hpow
  have hbad : μ.toOuterMeasure Eᶜ ≤ (2 : ENNReal)⁻¹ := by
    calc
      μ.toOuterMeasure Eᶜ = μ.toOuterMeasure (⋃ k, (G k)ᶜ) := by
        change μ.toOuterMeasure (⋂ k, G k)ᶜ = _
        rw [Set.compl_iInter]
      _ ≤ ∑ k, μ.toOuterMeasure (G k)ᶜ :=
        MeasureTheory.measure_iUnion_fintype_le μ.toOuterMeasure _
      _ ≤ ∑ _k : ι, (1 - a) ^ n := Finset.sum_le_sum fun k _ => hfail k
      _ = (Fintype.card ι : ENNReal) * (1 - a) ^ n := by simp
      _ ≤ (Δ : ENNReal) * (1 - a) ^ n :=
        mul_le_mul_right' (by exact_mod_cast hcard) _
      _ ≤ (2 : ENNReal)⁻¹ := hloss
  have hhalf : 1 - (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ :=
    ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top ENNReal.inv_two_add_inv_two.symm
  have hmass : (2 : ENNReal)⁻¹ ≤ μ.toOuterMeasure E := by
    calc
      (2 : ENNReal)⁻¹ = 1 - (2 : ENNReal)⁻¹ := hhalf.symm
      _ ≤ 1 - μ.toOuterMeasure Eᶜ := tsub_le_tsub_left hbad 1
      _ = μ.toOuterMeasure E := by rw [← hcompl, compl_compl]
  have hE : ∃ σ ∈ E, σ ∈ μ.support := by
    by_contra h
    have hz : μ.toOuterMeasure E = 0 :=
      (μ.toOuterMeasure_apply_eq_zero_iff E).2
        (Set.disjoint_left.2 fun σ hσ hσE => h ⟨σ, hσE, hσ⟩)
    rw [hz] at hmass
    norm_num at hmass
  have hratio : (C / (2 * n)) / (2 : ENNReal)⁻¹ = C / n := by
    rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc
      C * ((2 : ENNReal)⁻¹ * (n : ENNReal)⁻¹) * 2 =
          C * (n : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹ * 2) := by ac_rfl
      _ = C / n := by
        rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one,
          div_eq_mul_inv]
  refine ⟨E, ?_, hmass, hE, ?_⟩
  · intro σ
    exact Set.mem_iInter
  · have hconditioned := VertexSpreadConditioning E hE hspread
      (by norm_num : 0 < (2 : ENNReal)⁻¹) hmass (by rw [hratio]; exact hC)
    simpa only [hratio] using hconditioned
