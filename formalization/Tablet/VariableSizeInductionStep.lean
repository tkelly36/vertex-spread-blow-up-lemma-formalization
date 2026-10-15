import Tablet.ColourRoundInvariant
import Tablet.ReducedSquareColoring
import Tablet.VertexSpreadSequential
import Tablet.NearEqualVaryingGoodEdgeSuperRegularity
import Tablet.DegreeCodegreeRegularityCriterion
import Tablet.ExtendUpdatedPartialEmbedding
import Tablet.MatchingInducedUpdatedCandidacyTransport
import Tablet.OneClusterExtension
import Tablet.RegularPairGoodCodegrees
import Tablet.VertexSpreadConditioning
import Tablet.VertexSpreadMonotone
import Tablet.MatchingInducedLeftRowDeletion
import Tablet.FutureExtraVertexStability
import Tablet.NearEqualFourGraphs
import Tablet.InductionApplicationCertificate
import Tablet.InstanceSuperRegular
import Tablet.SaturatingSourcePair
import Tablet.ColourRoundMatchingPreparation
import Tablet.ColourRoundKernelAssembly

-- [TABLET NODE: VariableSizeInductionStep]
theorem VariableSizeInductionStep :
    ∀ {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
      [DecidableEq VH] [DecidableEq VG]
      {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
      [DecidableRel G.Adj] [DecidableRel R.Adj]
      (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
      (colour : Fin r → Fin q)
      (theta density epsilon rho eta omega xi : ℕ → ENNReal)
      (D : ℕ) (d C a : ENNReal) (n round : ℕ)
      (cert : InductionApplicationCertificate D q d
        theta density epsilon rho eta omega xi),
      round < q →
      epsilon round ≤ epsilon (round + 1) →
      epsilon (round + 1) ≤ 1 →
      (∀ j : Fin r, (Finset.univ.filter fun k : Fin r => R.Adj j k).card ≤ D) →
      (∀ ⦃i j : Fin r⦄, i ≠ j →
        (R.Adj i j ∨ ∃ k : Fin r, R.Adj i k ∧ R.Adj k j) →
        colour i ≠ colour j) →
      (∀ j : Fin r,
        ((Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n ∨
         (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n + 1) ∧
        (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card =
          (Finset.univ.filter fun v : VG => B.hostCluster v = j).card) →
      InstanceSuperRegular B (epsilon 0) d →
      (∀ ⦃i j : Fin r⦄, R.Adj i j → SaturatingSourcePair B i j) →
      0 < a → a ≤ 1 → C / n ≤ 1 →
      D * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹ →
      2 * (eta round) ^ (2 : ℝ)⁻¹ ≤ theta round →
      eta round + D * (eta round) ^ (2 : ℝ)⁻¹ ≤ theta round →
      eta round + 2 * D * eta round ≤ theta round →
      (∀ x, x ≤ D → 0 < theta round ∧ 4 * theta round < rho x) →
      (∀ x, x ≤ D →
        2 * eta round < rho x ∧ 2 * eta round < 1 - rho x) →
      2 * eta round < d / 2 →
      2 * eta round < 1 - d / 2 →
      (∀ x, x < D → density (x + 1) = rho x * (d / 2)) →
      (∀ x, x < D →
        density (x + 1) + epsilon round + 1 / (n : ENNReal) ≤ density x) →
      omega (round + 1) < epsilon (round + 1) →
      (∀ x, x ≤ D →
        cert.witnessThinningThreshold round x ≤ n ∧
        cert.hostThinningThreshold round ≤ n ∧
        cert.matchingThreshold round x ≤ n ∧
        cert.matchingExistenceThreshold round x ≤ n ∧
        cert.matchingConstant round x ≤ C / 2) →
      (∀ x y, x ≤ D → y ≤ D →
        cert.fourGraphsThreshold round x y ≤ n ∧
        a ≤ cert.fourGraphsConstant round x y) →
      (n : ENNReal)⁻¹ ≤ xi round →
      xi round < eta round →
      xi round + 2 / (n : ENNReal) ≤ eta round →
      xi round + 1 / (eta round * (n : ENNReal)) ≤ eta round →
      (∀ x, x ≤ D →
        omega (round + 1) + 2 / (n : ENNReal) ≤ epsilon (round + 1) ∧
        omega (round + 1) + 1 / (epsilon (round + 1) * (n : ENNReal)) ≤ epsilon (round + 1)) →
      (∀ (touched : Finset (Fin r))
        (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X)),
        (∀ j ∈ touched, (colour j).val = round) →
        ColourRoundInvariant B A colour epsilon density D C n round touched X μ →
        ∀ i : Fin r, (colour i).val = round → i ∉ touched →
          let X' := Finset.univ.filter fun x : VH =>
            (colour (B.sourceCluster x)).val < round ∨
              B.sourceCluster x ∈ insert i touched
          let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
          ∃ κ : PartialCompatibleEmbedding B A X →
              PMF (PartialCompatibleEmbedding B A X'),
            (∀ f ∈ μ.support, ∀ h ∈ (κ f).support, ∀ x ∈ X,
              h.toFun x = f.toFun x) ∧
            (∀ f ∈ μ.support, VertexSpreadOn
              ((κ f).map fun h => fun y : {y : VH // y ∈ Y} => h.toFun y.1)
              (C / n) Set.univ) ∧
            ColourRoundInvariant B A colour epsilon density D C n round
              (insert i touched) X' (μ.bind κ)) := by
-- BODY
  intro r q VH VG _ _ _ _ H G R _ _ B A colour
    theta density epsilon rho eta omega xi D d C a n round cert
    hround herror herrorUnit hdegree hcolour hsizes hhost hsource
    ha haUnit hspreadUnit hloss hroot hregularityLoss hdegreeLoss
    hretainedDensity hwitnessDensity hhostLower hhostUpper hupdate hgap
    houtputError hscalar hordered hinteger hinner hinnerDegree hinnerRegularity houter
    touched X mu hS hinv i hi hiS
  let P : ColourRoundStepParameters D q d C a n round
      theta density epsilon rho eta omega xi := {
    certificate := cert
    round_bound := hround
    error_monotone := herror
    error_unit := herrorUnit
    probability_positive := ha
    probability_unit := haUnit
    spread_unit := hspreadUnit
    local_loss := hloss
    square_root_loss := hroot
    regularity_loss := hregularityLoss
    degree_loss := hdegreeLoss
    retained_density := hretainedDensity
    witness_density := hwitnessDensity
    host_density_lower := hhostLower
    host_density_upper := hhostUpper
    density_update := hupdate
    density_gap := hgap
    output_error := houtputError
    scalar_thresholds := hscalar
    ordered_thresholds := hordered
    integer_reserve := hinteger
    inner_reserve := hinner
    inner_degree_reserve := hinnerDegree
    inner_regularity_reserve := hinnerRegularity
    outer_reserve := houter }
  apply ColourRoundKernelAssembly B A colour epsilon density D C n round touched X mu hinv i hi hiS
  intro f hf
  obtain ⟨nu0, E, hE, _, _, hspread, hwitness⟩ :=
    ColourRoundMatchingPreparation B A colour theta density epsilon rho eta omega xi
      D d C a n round P hsizes hhost hsource touched X mu hinv i hi hiS f hf
  exact ⟨nu0.filter E hE, hspread, hwitness⟩
