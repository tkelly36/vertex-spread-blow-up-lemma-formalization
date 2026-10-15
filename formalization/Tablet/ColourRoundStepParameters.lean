import Tablet.InductionApplicationCertificate

universe u1 u2 u3 u4 u5

-- [TABLET NODE: ColourRoundStepParameters]
structure ColourRoundStepParameters
    (D q : ℕ) (d C a : ENNReal) (n round : ℕ)
    (theta density epsilon rho eta omega xi : ℕ → ENNReal) where
-- BODY
  certificate : InductionApplicationCertificate.{u1, u2, u3, u4, u5}
    D q d theta density epsilon rho eta omega xi
  round_bound : round < q
  error_monotone : epsilon round ≤ epsilon (round + 1)
  error_unit : epsilon (round + 1) ≤ 1
  probability_positive : 0 < a
  probability_unit : a ≤ 1
  spread_unit : C / n ≤ 1
  local_loss : D * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹
  square_root_loss : 2 * (eta round) ^ (2 : ℝ)⁻¹ ≤ theta round
  regularity_loss : eta round + D * (eta round) ^ (2 : ℝ)⁻¹ ≤ theta round
  degree_loss : eta round + 2 * D * eta round ≤ theta round
  retained_density : ∀ x, x ≤ D → 0 < theta round ∧ 4 * theta round < rho x
  witness_density : ∀ x, x ≤ D →
    2 * eta round < rho x ∧ 2 * eta round < 1 - rho x
  host_density_lower : 2 * eta round < d / 2
  host_density_upper : 2 * eta round < 1 - d / 2
  density_update : ∀ x, x < D → density (x + 1) = rho x * (d / 2)
  density_gap : ∀ x, x < D →
    density (x + 1) + epsilon round + 1 / (n : ENNReal) ≤ density x
  output_error : omega (round + 1) < epsilon (round + 1)
  scalar_thresholds : ∀ x, x ≤ D →
    certificate.witnessThinningThreshold round x ≤ n ∧
    certificate.hostThinningThreshold round ≤ n ∧
    certificate.matchingThreshold round x ≤ n ∧
    certificate.matchingExistenceThreshold round x ≤ n ∧
    certificate.matchingConstant round x ≤ C / 2
  ordered_thresholds : ∀ x y, x ≤ D → y ≤ D →
    certificate.fourGraphsThreshold round x y ≤ n ∧
    a ≤ certificate.fourGraphsConstant round x y
  integer_reserve : (n : ENNReal)⁻¹ ≤ xi round
  inner_reserve : xi round < eta round
  inner_degree_reserve : xi round + 2 / (n : ENNReal) ≤ eta round
  inner_regularity_reserve : xi round + 1 / (eta round * (n : ENNReal)) ≤ eta round
  outer_reserve : ∀ x, x ≤ D →
    omega (round + 1) + 2 / (n : ENNReal) ≤ epsilon (round + 1) ∧
    omega (round + 1) + 1 / (epsilon (round + 1) * (n : ENNReal)) ≤ epsilon (round + 1)
