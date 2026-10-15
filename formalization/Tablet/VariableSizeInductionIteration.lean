import Tablet.VariableSizeInductionBase
import Tablet.VariableSizeInductionStep
import Tablet.ColourClassSequentialCompletion
import Tablet.ColourRoundReset
import Tablet.ReducedSquareColoring

-- [TABLET NODE: VariableSizeInductionIteration]
theorem VariableSizeInductionIteration
    (d : ENNReal) (Delta : ℕ)
    (p rho epsilon omega theta zeta hatZeta : ℕ → ENNReal)
    (cert : InductionApplicationCertificate Delta (Delta ^ 2 + 1) d
      theta p epsilon rho zeta omega hatZeta)
    (a C : ENNReal) (n : ℕ)
    (hp : p 0 = d)
    (hrec : ∀ x, x < Delta → p (x + 1) = rho x * (d / 2))
    (ha : 0 < a) (ha1 : a ≤ 1) (hC : C / n ≤ 1)
    (hfailure : Delta * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹)
    (hstatic : ∀ s, s < Delta ^ 2 + 1 →
      epsilon s ≤ epsilon (s + 1) ∧ epsilon (s + 1) ≤ 1 ∧
      2 * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + Delta * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + 2 * Delta * zeta s ≤ theta s ∧
      (∀ x, x ≤ Delta → 0 < theta s ∧ 4 * theta s < rho x) ∧
      (∀ x, x ≤ Delta → 2 * zeta s < rho x ∧ 2 * zeta s < 1 - rho x) ∧
      2 * zeta s < d / 2 ∧ 2 * zeta s < 1 - d / 2 ∧
      (∀ x, x < Delta →
        p (x + 1) + epsilon s + 1 / (n : ENNReal) ≤ p x) ∧
      omega (s + 1) < epsilon (s + 1))
    (hthresholds : ∀ s, s < Delta ^ 2 + 1 →
      (∀ x, x ≤ Delta →
        cert.witnessThinningThreshold s x ≤ n ∧
        cert.hostThinningThreshold s ≤ n ∧
        cert.matchingThreshold s x ≤ n ∧
        cert.matchingExistenceThreshold s x ≤ n ∧
        cert.matchingConstant s x ≤ C / 2) ∧
      (∀ x y, x ≤ Delta → y ≤ Delta →
        cert.fourGraphsThreshold s x y ≤ n ∧
        a ≤ cert.fourGraphsConstant s x y))
    (hreserve : ∀ s, s < Delta ^ 2 + 1 →
      (n : ENNReal)⁻¹ ≤ hatZeta s ∧
      hatZeta s < zeta s ∧
      hatZeta s + 2 / (n : ENNReal) ≤ zeta s ∧
      hatZeta s + 1 / (zeta s * (n : ENNReal)) ≤ zeta s ∧
      omega (s + 1) + 2 / (n : ENNReal) ≤ epsilon (s + 1) ∧
      omega (s + 1) + 1 / (epsilon (s + 1) * (n : ENNReal)) ≤
        epsilon (s + 1)) :
    ∀ {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
      [DecidableEq VH] [DecidableEq VG]
      {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel G.Adj]
      {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
      (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B),
      (∀ j : Fin r,
        ((Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n ∨
         (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n + 1) ∧
        (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card =
          (Finset.univ.filter fun v : VG => B.hostCluster v = j).card) →
      R.maxDegree ≤ Delta →
      InstanceSuperRegular B (epsilon 0) d →
      CandidacySuperRegular B A (epsilon 0) d →
      (∀ ⦃i j : Fin r⦄, R.Adj i j → SaturatingSourcePair B i j) →
      ∃ (colour : Fin r → Fin (Delta ^ 2 + 1))
        (μ : PMF (PartialCompatibleEmbedding B A Finset.univ)),
        ColourRoundInvariant B A colour epsilon p Delta C n
          (Delta ^ 2)
          (Finset.univ.filter fun j : Fin r => (colour j).val = Delta ^ 2)
          Finset.univ μ := by
-- BODY
  classical
  intro r VH VG _ _ _ _ H G _ R _ B A hsizes hmax hG hA hsaturating
  let Q := Delta ^ 2 + 1
  have hQ : 0 < Q := Nat.zero_lt_succ _
  obtain ⟨q, _, hqQ, colour0, hcolour0⟩ := ReducedSquareColoring R hmax
  let colour : Fin r → Fin Q := fun j => Fin.castLE hqQ (colour0 j)
  have hcolour : ∀ ⦃i j : Fin r⦄, i ≠ j →
      (R.Adj i j ∨ ∃ k : Fin r, R.Adj i k ∧ R.Adj k j) →
      colour i ≠ colour j := by
    intro i j hij hadj heq
    exact hcolour0 hij hadj (Fin.castLE_injective hqQ heq)
  have hdegree (j : Fin r) :
      (Finset.univ.filter fun k : Fin r => R.Adj j k).card ≤ Delta := by
    have hneighbors : (Finset.univ.filter fun k : Fin r => R.Adj j k) =
        R.neighborFinset j := by
      ext k
      simp
    rw [hneighbors]
    exact (R.degree_le_maxDegree j).trans hmax
  let completedDomain (s : ℕ) : Finset VH := Finset.univ.filter fun x : VH =>
    (colour (B.sourceCluster x)).val < s ∨
      B.sourceCluster x ∈ Finset.univ.filter (fun j : Fin r => (colour j).val = s)
  have complete (s : ℕ) (hs : s < Q)
      (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X))
      (hμ : ColourRoundInvariant B A colour epsilon p Delta C n s ∅ X μ) :
      ∃ ν : PMF (PartialCompatibleEmbedding B A (completedDomain s)),
        ColourRoundInvariant B A colour epsilon p Delta C n s
          (Finset.univ.filter fun j : Fin r => (colour j).val = s)
          (completedDomain s) ν := by
    obtain ⟨hepsilon, hepsilon1, hsqrt, hregloss, hdegloss, htheta,
      hrho, hd, hdcomp, hgap, homega⟩ := hstatic s hs
    obtain ⟨hmatching, hfourgraphs⟩ := hthresholds s hs
    obtain ⟨hinv, hstrict, hpaddingDegree, hpaddingRegularity,
      houtputDegree, houtputRegularity⟩ := hreserve s hs
    have step := VariableSizeInductionStep B A colour theta p epsilon rho
      zeta omega hatZeta Delta d C a n s cert hs hepsilon hepsilon1
      hdegree hcolour hsizes hG hsaturating ha ha1 hC hfailure
      hsqrt hregloss hdegloss htheta hrho hd hdcomp hrec hgap homega
      hmatching hfourgraphs hinv hstrict hpaddingDegree hpaddingRegularity
      (fun x hx => ⟨houtputDegree, houtputRegularity⟩)
    obtain ⟨K, _, hK⟩ := ColourClassSequentialCompletion B A colour epsilon p
      Delta C n s step ∅ X μ (by simp) hμ
    exact ⟨μ.bind K, hK⟩
  have start (s : ℕ) (hs : s < Q) :
      ∃ (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X)),
        ColourRoundInvariant B A colour epsilon p Delta C n s ∅ X μ := by
    induction s with
    | zero =>
      obtain ⟨μ, hμ⟩ := VariableSizeInductionBase B A colour epsilon p
        Delta d C n hQ hp hC hdegree hcolour hA
      exact ⟨∅, μ, hμ⟩
    | succ s ih =>
      have hsold : s < Q := by omega
      obtain ⟨X, μ, hμ⟩ := ih hsold
      obtain ⟨ν, hν⟩ := complete s hsold X μ hμ
      exact ⟨completedDomain s, ν,
        ColourRoundReset B A colour epsilon p Delta C n s
          (completedDomain s) ν hs (hstatic s hsold).1 hν⟩
  have hlast : Delta ^ 2 < Q := Nat.lt_succ_self _
  obtain ⟨X, μ, hμ⟩ := start (Delta ^ 2) hlast
  have hfinal := complete (Delta ^ 2) hlast X μ hμ
  have hfull : completedDomain (Delta ^ 2) = Finset.univ := by
    ext x
    simp only [completedDomain, Finset.mem_filter, Finset.mem_univ, true_and]
    have hbound : (colour (B.sourceCluster x)).val ≤ Delta ^ 2 :=
      Nat.le_of_lt_succ (colour (B.sourceCluster x)).isLt
    exact iff_true_intro (lt_or_eq_of_le hbound)
  rw [hfull] at hfinal
  obtain ⟨ν, hν⟩ := hfinal
  exact ⟨colour, ν, hν⟩
