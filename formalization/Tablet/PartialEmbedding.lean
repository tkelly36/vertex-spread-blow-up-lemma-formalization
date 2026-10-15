import Tablet.InstanceLowerRegular
import Tablet.UpdatedCandidacyCluster
import Tablet.VertexSpreadSequential
import Tablet.PartialEmbeddingParameters
import Tablet.GreedyPartialEmbeddingStep
import Tablet.GreedyPartialEmbeddingReserve
import Tablet.FiniteGreedySpreadLaw
import Tablet.UpdatedCandidacyCongruence

-- [TABLET NODE: PartialEmbedding]
theorem PartialEmbedding :
    ∀ (Δ : ℕ) (d : ENNReal), 0 < d → d ≤ 1 →
      ∃ d₀' : ENNReal, 0 < d₀' ∧ d₀' < d ∧
      ∀ d' : ENNReal, 0 < d' → d' ≤ d₀' →
        ∃ ε₀ : ENNReal, 0 < ε₀ ∧ ε₀ < ⊤ ∧
        ∀ ε : ENNReal, 0 < ε → ε ≤ ε₀ →
          ∃ C₀ : ENNReal, 1 ≤ C₀ ∧ C₀ < ⊤ ∧
          ∀ C : ENNReal, C₀ ≤ C → C < ⊤ →
            ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
            ∀ {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
              [DecidableEq VH] [DecidableEq VG]
              {H : SimpleGraph VH} {G : SimpleGraph VG}
              [DecidableRel H.Adj] [DecidableRel G.Adj]
              {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
              (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
              [DecidableRel A.allowed],
              InstanceLowerRegular B ε d → H.maxDegree ≤ Δ → R.maxDegree ≤ Δ →
              (∀ i, (Fintype.card {x : VH // B.sourceCluster x = i} : ENNReal) ≤
                ε * Fintype.card {v : VG // B.hostCluster v = i}) →
              (∀ i, (1 - ε) * n ≤
                  Fintype.card {v : VG // B.hostCluster v = i} ∧
                (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤
                  (1 + ε) * n) →
              (∀ x, d * n ≤ Set.ncard {v : VG | A.allowed x v}) →
              (∃ μ : PMF {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ},
                VertexSpreadOn
                  (μ.map fun φ x => φ.1 x) (C / n) Set.univ) ∧
              (∀ X : Finset VH,
                ∃ μ : PMF {f : PartialCompatibleEmbedding B A X //
                    ∀ x, x ∉ X →
                      d' * n ≤ Set.ncard
                        {v : VG | (UpdatedCandidacy B A X f).allowed x v}},
                  VertexSpreadOn
                    (μ.map fun f => f.val.toFun) (C / n) Set.univ) := by
-- BODY
  classical
  intro Δ d hd hd1
  let a := d * (d / 2) ^ Δ
  obtain ⟨d₀', hd₀', hd₀'d, hp⟩ := PartialEmbeddingParameters Δ d hd hd1
  refine ⟨d₀', hd₀', hd₀'d, ?_⟩
  intro d' hd' hd'₀
  obtain ⟨ε₀, hε₀, hε₀top, hp⟩ := hp d' hd' hd'₀
  refine ⟨ε₀, hε₀, hε₀top, ?_⟩
  intro ε hε hε₀'
  obtain ⟨C₀, hC₀, hC₀top, hp⟩ := hp ε hε hε₀'
  refine ⟨C₀, hC₀, hC₀top, ?_⟩
  intro C hC hCtop
  obtain ⟨n₀, hp⟩ := hp C hC hCtop
  refine ⟨n₀, ?_⟩
  intro n hn₀
  obtain ⟨hn, hεhalf, hεd, ha, had, hpower, hthreshold, hloss,
    hd'a, hCa, hCtwo, hq, hrecip, hfallback⟩ := hp n hn₀
  intro r VH VG _ _ _ _ H G _ _ R _ B A _ hreg hdeg hR hsmall hhost hinit
  let q := C / n
  have hloss' : ε * (1 + ε) ≤ a / 2 := by
    calc
      ε * (1 + ε) = 1 * ε * (1 + ε) := by simp
      _ ≤ (Δ + 1 : ENNReal) * ε * (1 + ε) := by
        gcongr
        exact_mod_cast (Nat.le_add_left 1 Δ)
      _ ≤ a / 2 := hloss
  have hd'a' : d' ≤ a / 2 :=
    hd'a.trans (ENNReal.div_le_div le_rfl (by norm_num : (2 : ENNReal) ≤ 4))
  let Good : Finset VH → (VH → VG) → Prop := fun S f =>
    ∃ e : GreedyPartialEmbedding B A d ε n S, e.toFun = f
  have transfer : ∀ S f g, (∀ x ∈ S, f x = g x) → Good S f → Good S g := by
    intro S f g hfg he
    obtain ⟨e, he⟩ := he
    have heq : ∀ x ∈ S, e.toFun x = g x := fun x hx =>
      (congrFun he x).trans (hfg x hx)
    refine ⟨{
      toPartialCompatibleEmbedding := {
        toFun := g
        injOn := ?_
        map_adj := ?_
        compatible := ?_ }
      raw_bound := ?_ }, rfl⟩
    · intro x hx y hy hxy
      apply e.injOn hx hy
      rw [heq x hx, heq y hy]
      exact hxy
    · intro x y hx hy hxy
      rw [← heq x hx, ← heq y hy]
      exact e.map_adj hx hy hxy
    · intro x hx
      rw [← heq x hx]
      exact e.compatible x hx
    · intro x hx
      have hraw : RawCandidates B A S e.toFun x = RawCandidates B A S g x := by
        ext v
        simp only [RawCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hv, he'⟩
          refine ⟨hv, ?_⟩
          intro y hy hxy
          rw [← heq y hy]
          exact he' y hy hxy
        · rintro ⟨hv, he'⟩
          refine ⟨hv, ?_⟩
          intro y hy hxy
          rw [heq y hy]
          exact he' y hy hxy
      rw [← hraw]
      exact e.raw_bound x hx
  have hlocal : ∀ S f g, (∀ x ∈ S, f x = g x) → (Good S f ↔ Good S g) := by
    intro S f g hfg
    exact ⟨transfer S f g hfg, transfer S g f (fun x hx => (hfg x hx).symm)⟩
  have hzero : ∀ f, Good ∅ f := by
    intro f
    refine ⟨{
      toPartialCompatibleEmbedding := {
        toFun := f
        injOn := by simp
        map_adj := by simp
        compatible := by simp }
      raw_bound := ?_ }, rfl⟩
    intro x hx
    simpa [RawCandidates, Set.ncard_eq_toFinset_card'] using hinit x
  let T : VH → Finset VG := fun x =>
    Finset.univ.filter fun v => B.hostCluster v = B.sourceCluster x
  have hTcard (x : VH) : (T x).card =
      Fintype.card {v : VG // B.hostCluster v = B.sourceCluster x} := by
    simp [T, Fintype.card_subtype]
  have hTbound (x : VH) : 0 < (T x).card ∧ 1 / ((T x).card : ENNReal) ≤ q := by
    apply hfallback
    simpa only [hTcard] using (hhost (B.sourceCluster x)).1
  have hstep : ∀ S f z, z ∉ S → Good S f →
      ∃ L : Finset VG, L.Nonempty ∧ 1 / (L.card : ENNReal) ≤ q ∧
        ∀ v ∈ L, Good (insert z S) (Function.update f z v) := by
    intro S f z hz he
    obtain ⟨e, he⟩ := he
    obtain ⟨L, hL, hLsize, hLstep⟩ := GreedyPartialEmbeddingStep Δ d ε a n hn ha
      hpower hthreshold hloss B A hreg hdeg hsmall (fun i => (hhost i).2) S e z hz
    refine ⟨L, hL, hrecip L.card hLsize, ?_⟩
    intro v hv
    obtain ⟨g, hg⟩ := hLstep v hv
    exact ⟨g, hg.trans (congrArg (fun f => Function.update f z v) he)⟩
  have law (X : Finset VH) : ∃ μ : PMF {f : VH → VG // Good X f},
      VertexSpreadOn (μ.map Subtype.val) q Set.univ :=
    FiniteGreedySpreadLaw q hq T (fun x => Finset.card_pos.mp (hTbound x).1)
      (fun x => (hTbound x).2) Good hlocal hzero hstep X
  constructor
  · obtain ⟨μ, hμ⟩ := law Finset.univ
    let pack : {f : VH → VG // Good Finset.univ f} →
        {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ} := fun u =>
      let e := Classical.choose u.property
      ⟨{
         toHom := {
           toFun := e.toFun
           map_rel' := fun hxy => e.map_adj (Finset.mem_univ _) (Finset.mem_univ _) hxy }
         injective' := fun x y hxy => e.injOn (Finset.mem_univ x) (Finset.mem_univ y) hxy },
       fun x => e.compatible x (Finset.mem_univ x)⟩
    refine ⟨μ.map pack, ?_⟩
    have hm : (μ.map pack).map (fun φ x => φ.1 x) = μ.map Subtype.val := by
      rw [PMF.map_comp]
      congr 1
      funext u
      exact Classical.choose_spec u.property
    rw [hm]
    exact hμ
  · intro X
    obtain ⟨μ, hμ⟩ := law X
    let pack : {f : VH → VG // Good X f} →
        {f : PartialCompatibleEmbedding B A X // ∀ x, x ∉ X →
          d' * n ≤ Set.ncard {v : VG | (UpdatedCandidacy B A X f).allowed x v}} := fun u =>
      let e := Classical.choose u.property
      ⟨e.toPartialCompatibleEmbedding,
       GreedyPartialEmbeddingReserve Δ d ε a d' n hpower hloss' hd'a' B A hdeg hsmall
         (fun i => (hhost i).2) X e⟩
    refine ⟨μ.map pack, ?_⟩
    have hm : (μ.map pack).map (fun f => f.val.toFun) = μ.map Subtype.val := by
      rw [PMF.map_comp]
      congr 1
      funext u
      exact Classical.choose_spec u.property
    rw [hm]
    exact hμ
