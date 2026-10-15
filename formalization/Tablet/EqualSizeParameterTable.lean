import Tablet.ExposureDensityRecursion
import Tablet.EqualSizeBackwardCertificates
import Tablet.EqualSizeCommonOrderBounds

-- [TABLET NODE: EqualSizeParameterTable]
theorem EqualSizeParameterTable :
    ∀ (d : ENNReal) (Delta : ℕ), 0 < d → d ≤ 1 →
      ∃ (p rho epsilon omega theta zeta hatZeta : ℕ → ENNReal)
        (cert : InductionApplicationCertificate Delta (Delta ^ 2 + 1) d
          theta p epsilon rho zeta omega hatZeta)
        (a M C : ENNReal) (n₀ : ℕ),
        p 0 = d ∧
        (∀ x, x ≤ Delta → 0 < p x ∧ p x ≤ 1 ∧ 0 < rho x ∧ rho x < p x) ∧
        (∀ x, x < Delta → p (x + 1) = rho x * (d / 2)) ∧
        (∀ s, s < Delta ^ 2 + 1 →
          0 < epsilon s ∧ epsilon s < hatZeta s ∧ hatZeta s < zeta s ∧
          0 < theta s ∧ 0 < omega (s + 1) ∧
          omega (s + 1) < epsilon (s + 1) ∧ epsilon s ≤ epsilon (s + 1) ∧
          epsilon (s + 1) ≤ 1 ∧
          2 * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
          zeta s + Delta * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
          zeta s + 2 * Delta * zeta s ≤ theta s ∧
          (∀ x, x ≤ Delta →
            4 * theta s < rho x ∧
            2 * zeta s < rho x ∧ 2 * zeta s < 1 - rho x) ∧
          2 * zeta s < d / 2 ∧ 2 * zeta s < 1 - d / 2 ∧
          (∀ y, y < Delta → 2 * epsilon s < p y - p (y + 1))) ∧
        0 < a ∧ a ≤ 1 ∧ 1 ≤ M ∧ 2 * M ≤ C ∧
        (∀ s, s < Delta ^ 2 + 1 →
          (∀ x, x ≤ Delta →
            a ≤ cert.fourGraphsConstant s x x ∧
            cert.matchingConstant s x ≤ M ∧
            cert.witnessThinningThreshold s x ≤ n₀ ∧
            cert.hostThinningThreshold s ≤ n₀ ∧
            cert.matchingThreshold s x ≤ n₀ ∧
            cert.matchingExistenceThreshold s x ≤ n₀) ∧
          (∀ x y, x ≤ Delta → y ≤ Delta →
            a ≤ cert.fourGraphsConstant s x y ∧
            cert.fourGraphsThreshold s x y ≤ n₀)) ∧
        (∀ n, n₀ ≤ n →
          C / (n : ENNReal) ≤ 1 ∧ Delta * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹ ∧
          ∀ s, s < Delta ^ 2 + 1 →
            (n : ENNReal)⁻¹ ≤ hatZeta s ∧
            (n : ENNReal)⁻¹ ≤ zeta s - hatZeta s ∧
            hatZeta s + 2 / (n : ENNReal) ≤ zeta s ∧
            hatZeta s + 1 / (zeta s * (n : ENNReal)) ≤ zeta s ∧
            omega (s + 1) + 2 / (n : ENNReal) ≤ epsilon (s + 1) ∧
            omega (s + 1) + 1 / (epsilon (s + 1) * (n : ENNReal)) ≤
              epsilon (s + 1)) := by
-- BODY
  intro d Delta hd hd1
  obtain ⟨p, rho, hp0, hdens, hrec, hgaps⟩ :=
    ExposureDensityRecursion d Delta hd hd1
  obtain ⟨epsilon, omega, theta, zeta, hatZeta, cert, hround, hfinite⟩ :=
    EqualSizeBackwardCertificates d Delta p rho hd hd1 hdens hgaps
  have hreserves : ∀ s, s < Delta ^ 2 + 1 →
      0 < hatZeta s ∧ hatZeta s < zeta s ∧ zeta s ≠ ⊤ ∧
      omega (s + 1) < epsilon (s + 1) ∧ epsilon (s + 1) ≤ 1 := by
    intro s hs
    obtain ⟨he, heh, hhz, ht, ho, hoe, hemono, he1,
      hroot, hsum, hlinear, hsmall, hdhalf, hdcomp, hgap⟩ := hround s hs
    have hz1 : zeta s ≤ 1 := by
      calc
        zeta s ≤ 2 * zeta s := by
          simpa using mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2) (zeta s)
        _ ≤ rho 0 := (hsmall 0 (Nat.zero_le Delta)).2.1.le
        _ ≤ 1 := (hdens 0 (Nat.zero_le Delta)).2.2.2.le.trans
          (hdens 0 (Nat.zero_le Delta)).2.1
    exact ⟨he.trans heh, hhz, ne_top_of_le_ne_top ENNReal.one_ne_top hz1, hoe, he1⟩
  obtain ⟨a, M, C, n₀, ha, ha1, hM, hC, hthresholds, horder⟩ :=
    EqualSizeCommonOrderBounds Delta d p rho epsilon omega theta zeta hatZeta
      cert hreserves hfinite
  exact ⟨p, rho, epsilon, omega, theta, zeta, hatZeta, cert,
    a, M, C, n₀, hp0, hdens, hrec, hround, ha, ha1, hM, hC, hthresholds, horder⟩
