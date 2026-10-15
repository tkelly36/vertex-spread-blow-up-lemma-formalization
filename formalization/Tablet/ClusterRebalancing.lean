import Tablet.ClusterwiseDeletionBuffer
import Tablet.RestrictedSmallBlowUpInterface
import Tablet.LowerSuperRegularDeletionSlicing
import Tablet.ExceptionalLeftLowerSuperRegular
import Tablet.CandidacyLowerSuperRegular
import Tablet.InstanceLowerSuperRegular
import Tablet.RebalancingLossMargins
import Tablet.RebalancingRestrictionEstimates
import Tablet.RestrictedPartialEmbeddingTransport
import Tablet.RebalancingResidualGeometry
import Tablet.RebalancingResidualHost
import Tablet.RebalancingResidualCandidacy

-- [TABLET NODE: ClusterRebalancing]
theorem ClusterRebalancing :
    ∀ (Delta : ℕ) (d : ENNReal), 1 ≤ Delta → 0 < d → d ≤ 1 →
      ∃ d₀' : ENNReal, 0 < d₀' ∧ d₀' < d ∧
      ∀ d' : ENNReal, 0 < d' → d' ≤ d₀' →
        ∃ epsilon₀' : ENNReal, 0 < epsilon₀' ∧
        ∀ epsilon' : ENNReal, 0 < epsilon' → epsilon' ≤ epsilon₀' →
          ∃ epsilon₀ : ENNReal, 0 < epsilon₀ ∧
          ∀ epsilon : ENNReal, 0 < epsilon → epsilon ≤ epsilon₀ →
            ∃ C₀ : ENNReal, 1 ≤ C₀ ∧ C₀ < ⊤ ∧
            ∀ C : ENNReal, C₀ ≤ C →
              ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → C / n ≤ 1 →
              ∀ {VH VG : Type*} [Fintype VH] [Fintype VG]
                [DecidableEq VH] [DecidableEq VG]
                {H : SimpleGraph VH} {G : SimpleGraph VG}
                [DecidableRel H.Adj] [DecidableRel G.Adj]
                {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
                (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
                [DecidableRel A.allowed],
                H.maxDegree ≤ Delta → R.maxDegree ≤ Delta →
                InstanceLowerSuperRegular B epsilon d →
                CandidacyLowerSuperRegular B A epsilon d →
                (∀ i, Fintype.card {x : VH // B.sourceCluster x = i} =
                  Fintype.card {v : VG // B.hostCluster v = i}) →
                (∀ i, (1 - epsilon) * n ≤
                    Fintype.card {v : VG // B.hostCluster v = i} ∧
                  (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤
                    (1 + epsilon) * n) →
                ∃ m : ℕ, (m : ENNReal) ≤ (1 - epsilon) * n ∧
                  (1 - epsilon) * n < (m : ENNReal) + 1 ∧
                ∃ X : Finset VH, ∃ μ : PMF (PartialCompatibleEmbedding B A X),
                  VertexSpreadOn
                    (μ.map (fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1))
                    (C / n) Set.univ ∧
                  ∀ f : PartialCompatibleEmbedding B A X, μ f ≠ 0 →
                    let Y := {x : VH // x ∉ X}
                    let W := {v : VG // v ∉ X.image f.toFun}
                    ∃ Br : BlowUpInstance r Y W
                        (H.induce {x : VH | x ∉ X})
                        (G.induce {v : VG | v ∉ X.image f.toFun}) R,
                    ∃ Ar : CandidacySystem Br,
                      (∀ x : Y, Br.sourceCluster x = B.sourceCluster x.1) ∧
                      (∀ v : W, Br.hostCluster v = B.hostCluster v.1) ∧
                      (∀ (x : Y) (v : W), Ar.allowed x v ↔
                        (UpdatedCandidacy B A X f).allowed x.1 v.1) ∧
                      (∀ i, Fintype.card {x : Y // Br.sourceCluster x = i} =
                        m) ∧
                      (∀ i, Fintype.card {v : W // Br.hostCluster v = i} =
                        m) ∧
                      InstanceLowerSuperRegular Br epsilon' d' ∧
                      CandidacyLowerSuperRegular Br Ar epsilon' d' := by
-- BODY
  classical
  intro Delta d hDelta hd hd1
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd1
  have hdhalf : 0 < d / 2 := ENNReal.half_pos hd.ne'
  obtain ⟨b, hb, hbd, hp⟩ := PartialEmbedding Delta (d / 2) hdhalf
    (ENNReal.half_le_self.trans hd1)
  let d₀' := min (d / 4) (b / 2)
  have hd₀' : 0 < d₀' := lt_min (ENNReal.div_pos hd.ne' (by norm_num))
    (ENNReal.half_pos hb.ne')
  have hdquarter : d / 4 ≤ d / 2 := ENNReal.div_le_div le_rfl (by norm_num)
  refine ⟨d₀', hd₀', (min_le_left _ _).trans_lt
    (hdquarter.trans_lt (ENNReal.half_lt_self hd.ne' hdtop)), ?_⟩
  intro d' hd' hd'₀
  have hd'd : d' ≤ d / 4 := hd'₀.trans (min_le_left _ _)
  have hd'b : d' ≤ b := hd'₀.trans ((min_le_right _ _).trans ENNReal.half_le_self)
  obtain ⟨a₀, ha₀, ha₀top, hp⟩ := hp d' hd' hd'b
  let a := min (1 / 4) (a₀ / 2)
  have ha : 0 < a := lt_min (by norm_num) (ENNReal.half_pos ha₀.ne')
  have haa₀ : a ≤ a₀ := (min_le_right _ _).trans ENNReal.half_le_self
  obtain ⟨ε₀', hε₀', hε₀'bound, hmargins⟩ :=
    RebalancingLossMargins Delta d d' a hDelta hd hd1 hd' hd'd ha (min_le_left _ _)
  refine ⟨ε₀', hε₀', ?_⟩
  intro ε' hε' hε'₀
  obtain ⟨ε₀, hε₀, hmargins⟩ := hmargins ε' hε' hε'₀
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  obtain ⟨na, hmargins⟩ := hmargins ε hε hε₀'
  obtain ⟨C₀, hC₀, hC₀top, hp⟩ := hp a ha haa₀
  refine ⟨C₀, hC₀, hC₀top, ?_⟩
  intro C hC
  by_cases hCtop : C = ⊤
  · subst C
    intro r
    refine ⟨4, ?_⟩
    intro n hn hq
    simp [ENNReal.top_div_of_ne_top (by simp : (n : ENNReal) ≠ ⊤)] at hq
  · obtain ⟨np, hp⟩ := hp C hC (lt_top_iff_ne_top.mpr hCtop)
    intro r
    refine ⟨max np na, ?_⟩
    intro n hn hq VH VG _ _ _ _ H G _ _ R _ B A _ hH hR hhost hcand hEq hsize
    obtain ⟨m, k, hn4, hεa, hεquarter, hεd, hε'top, hfloor, hceil,
      hmhalf, hmn, hkcast, hdensity, hN⟩ :=
      hmargins n ((le_max_right _ _).trans hn)
    have hN' (i : Fin r) := hN (Fintype.card {v : VG // B.hostCluster v = i})
      (hsize i).1 (hsize i).2
    have hm := fun i => (hN' i).1
    have hk := fun i => (hN' i).2.1
    have hloss := fun i => (hN' i).2.2.1
    have hsmall := fun i => (hN' i).2.2.2.1
    have hdegree := fun i => (hN' i).2.2.2.2.1
    have hthreshold := fun i => (hN' i).2.2.2.2.2.1
    have hhostdegree := fun i => (hN' i).2.2.2.2.2.2.1
    have hcanddegree := fun i => (hN' i).2.2.2.2.2.2.2
    obtain ⟨X, hXcount, _, hE⟩ :=
      ClusterwiseDeletionBuffer B m k Delta hEq hm hk hH hR
    let E := Finset.univ.filter fun x => x ∉ X ∧ ∃ y ∈ X, H.Adj x y
    let S := X ∪ E
    have hXloss (i : Fin r) :
        ((X.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤ 3 * ε * n := by
      rw [hXcount i]
      exact hloss i
    have hbuffer (i : Fin r) :
        ((E.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤
          4 * Delta * Delta * ε * n := by
      have hcast : ((E.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤
          (Delta : ENNReal) * Delta * k := by
        exact_mod_cast hE i
      calc
        _ ≤ (Delta : ENNReal) * Delta * k := hcast
        _ ≤ (Delta : ENNReal) * Delta * (4 * ε * n) := by gcongr
        _ = 4 * Delta * Delta * ε * n := by ac_rfl
    have hSsmall (i : Fin r) :
        ((S.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤
          a * Fintype.card {v : VG // B.hostCluster v = i} := by
      change (((X ∪ E).filter fun x => B.sourceCluster x = i).card : ENNReal) ≤ _
      rw [Finset.filter_union]
      have hc := Finset.card_union_le (X.filter fun x => B.sourceCluster x = i)
        (E.filter fun x => B.sourceCluster x = i)
      have hc' : (((X.filter fun x => B.sourceCluster x = i) ∪
          (E.filter fun x => B.sourceCluster x = i)).card : ENNReal) ≤
          ((X.filter fun x => B.sourceCluster x = i).card : ENNReal) +
          ((E.filter fun x => B.sourceCluster x = i).card : ENNReal) := by
        exact_mod_cast hc
      calc
        _ ≤ _ := hc'
        _ ≤ 3 * ε * n + 4 * Delta * Delta * ε * n :=
          add_le_add (hXloss i) (hbuffer i)
        _ = (3 + 4 * Delta * Delta) * ε * n := by simp only [add_mul]
        _ ≤ _ := hsmall i
    obtain ⟨hreg, hsizea, hinit⟩ :=
      RebalancingRestrictionEstimates B A n ε d a hεa hhost hcand hsize hdegree
    obtain ⟨Bs, As, hsm, hvm, ham, hrange, hsreg, hsH, hsR,
      hssmall, hssize, hsinit⟩ :=
      RestrictedSmallBlowUpInterface B A S Delta n a (d / 2) hreg hH hR hSsmall
        hsizea (fun x _ => hinit x)
    letI : DecidableRel As.allowed := fun _ _ => Classical.propDecidable _
    obtain ⟨_, hpartial⟩ := hp n ((le_max_left _ _).trans hn)
      Bs As hsreg hsH hsR hssmall hssize hsinit
    let T : Finset {x // x ∈ S} := Finset.univ.filter fun x => x.1 ∈ X
    obtain ⟨ν, hν⟩ := hpartial T
    have hnonempty (x : VH) : ∃ v, A.allowed x v := by
      have hnpos : 0 < (n : ENNReal) := by exact_mod_cast (by omega : 0 < n)
      have hmul : 0 < (d / 2) * n := by positivity
      have hpos := hmul.trans_le (hinit x)
      have hc : 0 < Set.ncard {v : VG | A.allowed x v} := by exact_mod_cast hpos
      exact (Set.ncard_pos (Set.toFinite _)).mp hc
    let g : VH → VG := fun x => Classical.choose (hnonempty x)
    obtain ⟨μ, hμ, hreserve⟩ := RestrictedPartialEmbeddingTransport B A S X
      Finset.subset_union_left Bs As ham T (by intro x; simp [T]) g (C / n) (d' * n) ν hν
    refine ⟨m, hfloor, hceil, X, μ, hμ, ?_⟩
    intro f hf
    obtain ⟨Br, Ar, hsource, hhostmap, hallowed, hleft, hright, hremoved⟩ :=
      RebalancingResidualGeometry B A X f m hEq hm hXcount
    have himageloss (i : Fin r) :
        (((X.image f.toFun).filter fun v => B.hostCluster v = i).card : ENNReal) ≤
          3 * ε * n := by
      rw [hremoved i]
      exact hXloss i
    have hresHost : InstanceLowerSuperRegular Br ε' d' :=
      RebalancingResidualHost B A X f Br m ε d ε' d' (3 * ε * n)
        hhostmap hright hhost himageloss hthreshold
        ((le_add_right le_rfl).trans hdensity) hhostdegree
    have hJ : 4 * Delta * Delta * ε * n ≤ (8 * Delta * Delta * ε) * m := by
      calc
        _ = (8 * Delta * Delta * ε) * ((n : ENNReal) / 2) := by
          simp only [div_eq_mul_inv]
          have htwo : (2⁻¹ : ENNReal) * 8 = 4 := by
            calc
              _ = (2⁻¹ : ENNReal) * (2 * 4) := by norm_num
              _ = ((2⁻¹ : ENNReal) * 2) * 4 := (mul_assoc _ _ _).symm
              _ = 4 := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
          calc
            4 * Delta * Delta * ε * n = (Delta : ENNReal) * Delta * ε * n * 4 := by ac_rfl
            _ = (Delta : ENNReal) * Delta * ε * n * ((2 : ENNReal)⁻¹ * 8) := by rw [htwo]
            _ = _ := by ac_rfl
        _ ≤ _ := by gcongr
    have hrho : (d' - ε') * m ≤ d' * n := by
      exact mul_le_mul' tsub_le_self (by exact_mod_cast hmn)
    have hresCand : CandidacyLowerSuperRegular Br Ar ε' d' :=
      RebalancingResidualCandidacy B A X f Br Ar m ε d ε' d'
        (3 * ε * n) (4 * Delta * Delta * ε * n) (8 * Delta * Delta * ε) (d' * n)
        hsource hhostmap hallowed hleft hright hEq hcand hXloss himageloss hbuffer
        hJ hε' hε'top hthreshold hdensity hcanddegree hrho
        (fun x hx hy => hreserve f hf x
          (Finset.mem_union_right X (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hy⟩)) hx)
    exact ⟨Br, Ar, hsource, hhostmap, hallowed, hleft, hright, hresHost, hresCand⟩
