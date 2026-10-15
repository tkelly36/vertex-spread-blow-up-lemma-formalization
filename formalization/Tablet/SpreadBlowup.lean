import Tablet.ClusterRebalancing
import Tablet.BlowUpReductionToAuxiliary
import Tablet.EqualSizeParameterTable
import Tablet.VariableSizeInductionIteration
import Tablet.EqualSizeTerminalConversion
import Tablet.RestrictReductionEmbedding
import Tablet.VertexSpreadSequential
import Tablet.SourceClusterPadding
import Tablet.AuxiliarySpreadExecution
import Tablet.BlowupOrderMargins
import Tablet.SupportedResidualComposition

-- [TABLET NODE: SpreadBlowup]
theorem SpreadBlowup :
    ∀ (d : ENNReal) (Delta : ℕ), 0 < d → d ≤ 1 → 1 ≤ Delta →
      ∃ (epsilon C : ENNReal), 0 < epsilon ∧ epsilon < 1 ∧ 1 ≤ C ∧
      ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ {VH VG : Type*} [Fintype VH] [Fintype VG]
        [DecidableEq VH] [DecidableEq VG]
        {H : SimpleGraph VH} {G : SimpleGraph VG}
        [DecidableRel H.Adj] [DecidableRel G.Adj]
        {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
        (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B),
        H.maxDegree ≤ Delta → R.maxDegree ≤ Delta →
        InstanceLowerSuperRegular B epsilon d →
        CandidacyLowerSuperRegular B A epsilon d →
        (∀ i, (1 - epsilon) * n ≤
            Fintype.card {v : VG // B.hostCluster v = i} ∧
          (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤
            (1 + epsilon) * n) →
        ∃ μ : PMF {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ},
          VertexSpreadOn (μ.map fun φ => fun x => φ.1 x) (C / n) Set.univ := by
-- BODY
  classical
  intro d Delta hd hd1 hDelta
  obtain ⟨d₁, hd₁, hd₁d, hbal⟩ := ClusterRebalancing Delta d hDelta hd hd1
  have hd₁one : d₁ ≤ 1 := hd₁d.le.trans hd1
  obtain ⟨ε₀', hε₀', hbal⟩ := hbal d₁ hd₁ le_rfl
  let d₂ := (d₁ ^ 2 / 2) / 2
  have hp : 0 < d₁ ^ 2 / 2 := ENNReal.half_pos (ENNReal.pow_pos hd₁ 2).ne'
  have hpone : d₁ ^ 2 / 2 ≤ 1 :=
    ENNReal.half_le_self.trans (pow_le_one₀ (zero_le _) hd₁one)
  have hd₂ : 0 < d₂ := ENNReal.half_pos hp.ne'
  have hd₂lt : d₂ < d₁ ^ 2 / 2 :=
    ENNReal.half_lt_self hp.ne' (ne_top_of_le_ne_top (by simp) hpone)
  have hd₂one : d₂ ≤ 1 := ENNReal.half_le_self.trans hpone
  obtain ⟨ε₂, C', Nexec, hε₂, hε₂one, hC', hC'top, hNexec, hexec⟩ :=
    AuxiliarySpreadExecution d₂ (Delta ^ 3) hd₂ hd₂one
  obtain ⟨εred, hεred, _, hred⟩ := BlowUpReductionToAuxiliary Delta ε₂ d₂ d₁
    hDelta hε₂ hε₂one hd₂ hd₂lt hd₁one
  let ε₁ := min ε₀' εred
  have hε₁ : 0 < ε₁ := lt_min hε₀' hεred
  obtain ⟨ε₀, hε₀, hbal⟩ := hbal ε₁ hε₁ (min_le_left _ _)
  let η := min ε₀ (1 / 2)
  have hη : 0 < η := lt_min hε₀ (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηone : η ≤ 1 := hηhalf.trans (by norm_num)
  obtain ⟨C₀, hC₀, hC₀top, hbal⟩ := hbal η hη (min_le_left _ _)
  obtain ⟨C, hC, hCtop, hCC₀, hmargins⟩ :=
    BlowupOrderMargins η C₀ C' (Delta ^ 2) hη hηhalf hC₀ hC₀top hC'top
      (one_le_pow₀ hDelta)
  let ε := η * η
  have hε : 0 < ε := ENNReal.mul_pos hη.ne' hη.ne'
  have hεη : ε ≤ η := by
    simpa only [mul_one] using mul_le_mul_left' hηone η
  refine ⟨ε, C, hε, hεη.trans_lt (hηhalf.trans_lt (by norm_num)), hC, ?_⟩
  intro r
  obtain ⟨Nbal, hbal⟩ := hbal C hCC₀ r
  obtain ⟨Nred, hred⟩ := hred r
  obtain ⟨N, hN⟩ := hmargins Nbal Nred Nexec
  refine ⟨N, ?_⟩
  intro n hn VH VG _ _ _ _ H G _ _ R _ B A hH hR hhost hcand hsize
  letI : DecidableRel A.allowed := fun _ _ => Classical.propDecidable _
  obtain ⟨hnBal, hq, hmargins⟩ := hN n hn
  obtain ⟨Hp, hHp, Bp, Ap, hAp, hold, _, _, _, hhostmap, _, _,
    hEq, hmax, hpadhost, hpadcand, _, hunpad⟩ :=
    SourceClusterPadding B A ε η d hε le_rfl hηone hd1 hcand
  letI : DecidableRel Hp.Adj := hHp
  letI : DecidableRel Ap.allowed := hAp
  have hhη : InstanceLowerSuperRegular B η d := by
    intro i j hij
    obtain ⟨hreg, hl, hr⟩ := hhost hij
    refine ⟨?_, ?_, ?_⟩
    · intro U hU T hT hsizeU hsizeT
      exact (tsub_le_tsub_left hεη d).trans (hreg U hU T hT
        ((mul_le_mul_right' hεη _).trans_lt hsizeU)
        ((mul_le_mul_right' hεη _).trans_lt hsizeT))
    · intro v hv
      exact (mul_le_mul_right' (tsub_le_tsub_left hεη d) _).trans (hl v hv)
    · intro v hv
      exact (mul_le_mul_right' (tsub_le_tsub_left hεη d) _).trans (hr v hv)
  have hsizep : ∀ i,
      (1 - η) * n ≤ Fintype.card {v : VG // Bp.hostCluster v = i} ∧
      (Fintype.card {v : VG // Bp.hostCluster v = i} : ENNReal) ≤ (1 + η) * n := by
    intro i
    have heq : Fintype.card {v : VG // Bp.hostCluster v = i} =
        Fintype.card {v : VG // B.hostCluster v = i} := by
      simp only [Fintype.card_subtype, hhostmap]
    rw [heq]
    exact ⟨(mul_le_mul_right' (tsub_le_tsub_left hεη 1) _).trans (hsize i).1,
      (hsize i).2.trans (mul_le_mul_right' (add_le_add le_rfl hεη) _)⟩
  obtain ⟨m, hmlo, hmhi, X, μ, hμ, hres⟩ := hbal n hnBal hq Bp Ap
    (hmax.trans hH) hR (hpadhost η hhη) hpadcand hEq hsizep
  obtain ⟨hmred, hmexec, hratio⟩ := hmargins m hmlo hmhi
  have hcomplete : ∃ ν : PMF {φ : SimpleGraph.Copy Hp G // CompatibleEmbedding Bp Ap φ},
      VertexSpreadOn (ν.map fun φ => fun x => φ.1 x) (C / n) Set.univ := by
    apply SupportedResidualComposition Bp Ap X μ (C / n) hμ
    intro f hf
    obtain ⟨Br, Ar, hsourcemap, hhostmapr, hallowed, hsizes, hsizev, hrhost, hrcand⟩ :=
      hres f hf
    let Y := {x : PaddedSource B // x ∉ X}
    let W := {v : VG // v ∉ X.image f.toFun}
    letI : DecidableRel Ar.allowed := fun _ _ => Classical.propDecidable _
    have hHr : (Hp.induce {x | x ∉ X}).maxDegree ≤ Delta := by
      let inc : SimpleGraph.Copy (Hp.induce {x | x ∉ X}) Hp := {
        toHom := { toFun := Subtype.val, map_rel' := fun h => h }
        injective' := Subtype.val_injective }
      exact inc.max_degree_le.trans (hmax.trans hH)
    have hrhost' : InstanceLowerSuperRegular Br εred d₁ := by
      intro i j hij
      obtain ⟨hreg, hl, hr⟩ := hrhost hij
      have hee : ε₁ ≤ εred := min_le_right _ _
      refine ⟨?_, ?_, ?_⟩
      · intro U hU T hT hsizeU hsizeT
        exact (tsub_le_tsub_left hee d₁).trans (hreg U hU T hT
          ((mul_le_mul_right' hee _).trans_lt hsizeU)
          ((mul_le_mul_right' hee _).trans_lt hsizeT))
      · intro v hv
        exact (mul_le_mul_right' (tsub_le_tsub_left hee d₁) _).trans (hl v hv)
      · intro v hv
        exact (mul_le_mul_right' (tsub_le_tsub_left hee d₁) _).trans (hr v hv)
    have hrcand' : CandidacyLowerSuperRegular Br Ar εred d₁ := by
      intro i
      obtain ⟨hreg, hl, hr⟩ := hrcand i
      have hee : ε₁ ≤ εred := min_le_right _ _
      refine ⟨?_, ?_, ?_⟩
      · intro U hU T hT hsizeU hsizeT
        exact (tsub_le_tsub_left hee d₁).trans (hreg U hU T hT
          ((mul_le_mul_right' hee _).trans_lt hsizeU)
          ((mul_le_mul_right' hee _).trans_lt hsizeT))
      · intro v hv
        exact (mul_le_mul_right' (tsub_le_tsub_left hee d₁) _).trans (hl v hv)
      · intro v hv
        exact (mul_le_mul_right' (tsub_le_tsub_left hee d₁) _).trans (hr v hv)
    have hcounts : ∀ i,
        (Finset.univ.filter fun x : Y => Br.sourceCluster x = i).card = m ∧
        (Finset.univ.filter fun v : W => Br.hostCluster v = i).card = m := by
      intro i
      simpa only [Fintype.card_subtype] using And.intro (hsizes i) (hsizev i)
    obtain ⟨H', G', R', hH', hG', hR', B', A', hHle, hGle, hAle,
      hsmap, hvmap, hparts, _, _, hRmax, hreg, hareg, hsat⟩ :=
      hred m hmred Br Ar hcounts hHr hR hrhost' hrcand'
    letI : DecidableRel H'.Adj := hH'
    letI : DecidableRel G'.Adj := hG'
    letI : DecidableRel R'.Adj := hR'
    have hRcomap : (R'.comap finProdFinEquiv.symm).maxDegree ≤ Delta ^ 3 := by
      let inc : SimpleGraph.Copy (R'.comap finProdFinEquiv.symm) R' := {
        toHom := { toFun := finProdFinEquiv.symm, map_rel' := fun h => h }
        injective' := finProdFinEquiv.symm.injective }
      exact inc.max_degree_le.trans hRmax
    have hpartcounts : ∀ j,
        ((Finset.univ.filter fun x : Y => B'.sourceCluster x = j).card = m / Delta ^ 2 ∨
         (Finset.univ.filter fun x : Y => B'.sourceCluster x = j).card = m / Delta ^ 2 + 1) ∧
        (Finset.univ.filter fun x : Y => B'.sourceCluster x = j).card =
          (Finset.univ.filter fun v : W => B'.hostCluster v = j).card := by
      intro j
      have hp := hparts (finProdFinEquiv.symm j)
      simpa only [Equiv.apply_symm_apply] using And.intro hp.2 hp.1
    have hsat' : ∀ ⦃i j⦄, (R'.comap finProdFinEquiv.symm).Adj i j →
        SaturatingSourcePair B' i j := by
      intro i j hij
      simpa only [Equiv.apply_symm_apply] using
        hsat (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) hij
    obtain ⟨ν, hν⟩ := hexec (r * Delta ^ 2) (m / Delta ^ 2) hmexec B' A'
      hpartcounts hRcomap hreg hareg hsat'
    let F : {φ : SimpleGraph.Copy H' G' // CompatibleEmbedding B' A' φ} →
        {φ : SimpleGraph.Copy (Hp.induce {x | x ∉ X})
          (G.induce {v | v ∉ X.image f.toFun}) // CompatibleEmbedding Br Ar φ} := fun φ => by
      let g := RestrictReductionEmbedding Br Ar B' A' hHle hGle hAle hsmap hvmap φ.1 φ.2
      exact ⟨{
        toHom := {
          toFun := g.toFun
          map_rel' := fun h => g.map_adj (Finset.mem_univ _) (Finset.mem_univ _) h }
        injective' := fun _ _ h => g.injOn (Finset.mem_univ _) (Finset.mem_univ _) h },
        fun x => g.compatible x (Finset.mem_univ _)⟩
    refine ⟨Br, Ar, hsourcemap, hhostmapr, hallowed, ν.map F, ?_⟩
    have hspread : VertexSpreadOn ((ν.map F).map fun φ => fun x => φ.1 x)
        (C' / (m / Delta ^ 2 : ℕ)) Set.univ := by
      simpa only [PMF.map_comp, Function.comp_def, F, RestrictReductionEmbedding] using hν
    refine ⟨hq, ?_⟩
    intro s x y hx hy
    exact (hspread.2 s x y hx hy).trans (pow_le_pow_left' hratio s)
  obtain ⟨ν, hν⟩ := hcomplete
  exact hunpad (C / n) ν hν
