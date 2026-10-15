import Tablet.EqualSizeOneRoundChoices
import Tablet.SuperRegularErrorMonotone

-- [TABLET NODE: EqualSizeBackwardCertificates]
theorem EqualSizeBackwardCertificates (d : ENNReal) (Delta : ℕ)
    (p rho : ℕ → ENNReal) (hd : 0 < d) (hd1 : d ≤ 1)
    (hdens : ∀ x, x ≤ Delta →
      0 < p x ∧ p x ≤ 1 ∧ 0 < rho x ∧ rho x < p x)
    (hgaps : ∀ y, y < Delta → 0 < p y - p (y + 1)) :
    ∃ (epsilon omega theta zeta hatZeta : ℕ → ENNReal)
      (cert : InductionApplicationCertificate Delta (Delta ^ 2 + 1) d
        theta p epsilon rho zeta omega hatZeta),
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
      (∀ s x, s < Delta ^ 2 + 1 → x ≤ Delta →
        cert.matchingConstant s x ≠ ⊤) := by
-- BODY
  classical
  let Q := Delta ^ 2 + 1
  let E := {e : ENNReal // 0 < e ∧ e ≤ 1}
  have hchoices (e : E) := EqualSizeOneRoundChoices d Delta p rho e.val
    hd hd1 e.property.1 e.property.2 hdens hgaps
  choose om th ze hz cut pkg hdata using hchoices
  have hcut (e : E) : 0 < cut e ∧ cut e ≤ e.val := by
    obtain ⟨hb, _, _, _, _, _, hbe, _⟩ := hdata e
    exact ⟨hb, hbe⟩
  have half_le (b : ENNReal) : b / 2 ≤ b := by
    calc
      b / 2 = b * (2 : ENNReal)⁻¹ := rfl
      _ ≤ b * 1 := mul_le_mul_left' (by norm_num) b
      _ = b := mul_one b
  let step (e : E) : E := ⟨cut e / 2,
    ENNReal.div_pos (hcut e).1.ne' (by norm_num),
    (half_le _).trans ((hcut e).2.trans e.property.2)⟩
  let chain : ℕ → E := fun k => Nat.rec
    (⟨1 / 2, by norm_num, by norm_num⟩ : E) (fun _ e => step e) k
  have hchain (k : ℕ) : (chain (k + 1)).val = cut (chain k) / 2 := rfl
  let input (s : ℕ) : E := chain (Q - (s + 1))
  letI : Nonempty (Fin Q) := ⟨⟨0, by dsimp [Q]; omega⟩⟩
  let bmin := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin Q => cut (input i))
  have hbmin : 0 < bmin := (Finset.lt_inf'_iff _).mpr
    (fun i _ => (hcut (input i)).1)
  let epsilon (s : ℕ) := if s = 0 then bmin / 2 else (chain (Q - s)).val
  let omega (s : ℕ) := om (chain (Q - s))
  let theta (s : ℕ) := th (input s)
  let zeta (s : ℕ) := ze (input s)
  let hatZeta (s : ℕ) := hz (input s)
  have hepspos (s : ℕ) : 0 < epsilon s := by
    dsimp only [epsilon]
    split
    · exact ENNReal.div_pos hbmin.ne' (by norm_num)
    · exact (chain (Q - s)).property.1
  have hepsnext (s : ℕ) : epsilon (s + 1) = (input s).val := by
    simp only [epsilon, Nat.add_eq_zero, Nat.one_ne_zero, and_false, if_false, input]
  have hepszero (s : ℕ) (hs : s < Q) : epsilon 0 ≤ cut (input s) := by
    change bmin / 2 ≤ cut (input s)
    exact (half_le _).trans
      (Finset.inf'_le _ (Finset.mem_univ (⟨s, hs⟩ : Fin Q)))
  have hepscut (s : ℕ) (hs : s < Q) : epsilon s ≤ cut (input s) := by
    by_cases hs0 : s = 0
    · subst s
      exact hepszero 0 hs
    · have hidx : Q - s = Q - (s + 1) + 1 := by omega
      simp only [epsilon, if_neg hs0, hidx, hchain]
      exact half_le _
  have hround (s : ℕ) (hs : s < Q) :
      0 < epsilon s ∧ epsilon s < hatZeta s ∧ hatZeta s < zeta s ∧
      0 < theta s ∧ 0 < omega (s + 1) ∧
      omega (s + 1) < epsilon (s + 1) ∧ epsilon s ≤ epsilon (s + 1) ∧
      epsilon (s + 1) ≤ 1 ∧
      2 * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + Delta * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + 2 * Delta * zeta s ≤ theta s ∧
      (∀ x, x ≤ Delta →
        4 * theta s < rho x ∧ 2 * zeta s < rho x ∧ 2 * zeta s < 1 - rho x) ∧
      2 * zeta s < d / 2 ∧ 2 * zeta s < 1 - d / 2 ∧
      (∀ y, y < Delta → 2 * epsilon s < p y - p (y + 1)) := by
    obtain ⟨hb, hbh, hhz, ht, ho, hoe, hbe, hroot, hsum, hlinear,
      hsmall, hhalf, hcompl, hgap, _⟩ := hdata (input s)
    have he := hepscut s hs
    refine ⟨hepspos s, he.trans_lt hbh, hhz, ht, ho, ?_, ?_, ?_,
      hroot, hsum, hlinear, hsmall, hhalf, hcompl, ?_⟩
    · rw [hepsnext]
      exact hoe
    · rw [hepsnext]
      exact he.trans hbe
    · rw [hepsnext]
      exact (input s).property.2
    · intro y hy
      exact (mul_le_mul_left' he 2).trans_lt (hgap y hy)
  let cert : InductionApplicationCertificate Delta Q d
      theta p epsilon rho zeta omega hatZeta := {
    witnessThinningThreshold := fun s x => (pkg (input s)).witnessThinningThreshold 0 x
    hostThinningThreshold := fun s => (pkg (input s)).hostThinningThreshold 0
    fourGraphsConstant := fun s x y => (pkg (input s)).fourGraphsConstant 0 x y
    fourGraphsThreshold := fun s x y => (pkg (input s)).fourGraphsThreshold 0 x y
    matchingConstant := fun s x => (pkg (input s)).matchingConstant 0 x
    matchingThreshold := fun s x => (pkg (input s)).matchingThreshold 0 x
    matchingExistenceThreshold := fun s x => (pkg (input s)).matchingExistenceThreshold 0 x
    witnessThinningGuarantee := by
      intro s hs x hx V _ _ G _ L R hLR hL hR hnearL hnearR hG
      exact (pkg (input s)).witnessThinningGuarantee 0 (by norm_num) x hx G L R
        hLR hL hR hnearL hnearR
        (SuperRegularErrorMonotone G L R _ _ _ (hepscut s hs) hG)
    hostThinningGuarantee := by
      intro s hs V _ _ G _ L R hLR hL hR hnearL hnearR hG
      exact (pkg (input s)).hostThinningGuarantee 0 (by norm_num) G L R
        hLR hL hR hnearL hnearR
        (SuperRegularErrorMonotone G L R _ _ _ (hepszero s hs) hG)
    fourGraphsPositive := by
      intro s hs x y hx hy
      exact (pkg (input s)).fourGraphsPositive 0 (by norm_num) x y hx hy
    fourGraphsGuarantee := by
      intro s hs x y hx hy
      exact (pkg (input s)).fourGraphsGuarantee 0 (by norm_num) x y hx hy
    matchingConstantAtLeastOne := by
      intro s hs x hx
      exact (pkg (input s)).matchingConstantAtLeastOne 0 (by norm_num) x hx
    matchingExistenceGuarantee := by
      intro s hs x hx
      exact (pkg (input s)).matchingExistenceGuarantee 0 (by norm_num) x hx
    matchingGuarantee := by
      intro s hs x hx
      exact (pkg (input s)).matchingGuarantee 0 (by norm_num) x hx
  }
  refine ⟨epsilon, omega, theta, zeta, hatZeta, cert, hround, ?_⟩
  intro s x hs hx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hfin⟩ := hdata (input s)
  exact hfin x hx
