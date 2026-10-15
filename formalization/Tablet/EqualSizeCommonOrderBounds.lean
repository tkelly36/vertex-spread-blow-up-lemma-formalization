import Tablet.InductionApplicationCertificate
import Mathlib.Analysis.SpecificLimits.Basic

open Filter

-- [TABLET NODE: EqualSizeCommonOrderBounds]
theorem EqualSizeCommonOrderBounds (Delta : ℕ) (d : ENNReal)
    (p rho epsilon omega theta zeta hatZeta : ℕ → ENNReal)
    (cert : InductionApplicationCertificate Delta (Delta ^ 2 + 1) d
      theta p epsilon rho zeta omega hatZeta)
    (hreserves : ∀ s, s < Delta ^ 2 + 1 →
      0 < hatZeta s ∧ hatZeta s < zeta s ∧ zeta s ≠ ⊤ ∧
      omega (s + 1) < epsilon (s + 1) ∧ epsilon (s + 1) ≤ 1)
    (hfinite : ∀ s x, s < Delta ^ 2 + 1 → x ≤ Delta →
      cert.matchingConstant s x ≠ ⊤) :
    ∃ (a M C : ENNReal) (n₀ : ℕ),
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
  classical
  let Q := Delta ^ 2 + 1
  letI : Nonempty (Fin Q) := ⟨⟨0, by dsimp [Q]; omega⟩⟩
  let A := Fin Q × (Fin (Delta + 1) × Fin (Delta + 1))
  let B := Fin Q × Fin (Delta + 1)
  let f : A → ENNReal := fun i => cert.fourGraphsConstant i.1 i.2.1 i.2.2
  let g : B → ENNReal := fun i => cert.matchingConstant i.1 i.2
  let a := min 1 (Finset.univ.inf' Finset.univ_nonempty f)
  let M := max 1 (Finset.univ.sup g)
  let C := 2 * M
  have ha : 0 < a := by
    refine lt_min (by norm_num) ((Finset.lt_inf'_iff _).mpr ?_)
    intro i _
    exact (cert.fourGraphsPositive i.1 i.1.isLt i.2.1 i.2.2
      (by omega) (by omega)).1
  have ha1 : a ≤ 1 := min_le_left _ _
  have haconst (s x y : ℕ) (hs : s < Q) (hx : x ≤ Delta) (hy : y ≤ Delta) :
      a ≤ cert.fourGraphsConstant s x y := by
    exact (min_le_right _ _).trans
      (Finset.inf'_le f (Finset.mem_univ (⟨⟨s, hs⟩, ⟨x, by omega⟩, ⟨y, by omega⟩⟩ : A)))
  have hM : 1 ≤ M := le_max_left _ _
  have hMconst (s x : ℕ) (hs : s < Q) (hx : x ≤ Delta) :
      cert.matchingConstant s x ≤ M := by
    exact (Finset.le_sup (f := g) (Finset.mem_univ (⟨⟨s, hs⟩, ⟨x, by omega⟩⟩ : B))).trans
      (le_max_right _ _)
  have hMtop : M ≠ ⊤ := by
    apply ne_of_lt
    refine max_lt (by simp) ((Finset.sup_lt_iff (by simp)).mpr ?_)
    intro i _
    exact lt_top_iff_ne_top.mpr (hfinite i.1 i.2 i.1.isLt (by omega))
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hMtop
  let Ncert : ℕ := Finset.univ.sup fun i : A =>
    max (cert.witnessThinningThreshold i.1 i.2.1)
      (max (cert.hostThinningThreshold i.1)
        (max (cert.matchingThreshold i.1 i.2.1)
          (max (cert.matchingExistenceThreshold i.1 i.2.1)
            (cert.fourGraphsThreshold i.1 i.2.1 i.2.2))))
  have hNcert (s x y : ℕ) (hs : s < Q) (hx : x ≤ Delta) (hy : y ≤ Delta) :
      cert.witnessThinningThreshold s x ≤ Ncert ∧
      cert.hostThinningThreshold s ≤ Ncert ∧
      cert.matchingThreshold s x ≤ Ncert ∧
      cert.matchingExistenceThreshold s x ≤ Ncert ∧
      cert.fourGraphsThreshold s x y ≤ Ncert := by
    have h := Finset.le_sup (f := fun i : A =>
      max (cert.witnessThinningThreshold i.1 i.2.1)
        (max (cert.hostThinningThreshold i.1)
          (max (cert.matchingThreshold i.1 i.2.1)
            (max (cert.matchingExistenceThreshold i.1 i.2.1)
              (cert.fourGraphsThreshold i.1 i.2.1 i.2.2)))))
      (Finset.mem_univ (⟨⟨s, hs⟩, ⟨x, by omega⟩, ⟨y, by omega⟩⟩ : A))
    change max (cert.witnessThinningThreshold s x)
      (max (cert.hostThinningThreshold s)
        (max (cert.matchingThreshold s x)
          (max (cert.matchingExistenceThreshold s x)
            (cert.fourGraphsThreshold s x y)))) ≤ Ncert at h
    omega
  have hsmall (c r : ENNReal) (hc : c ≠ ⊤) (hr : 0 < r) :
      ∀ᶠ n : ℕ in atTop, c * (n : ENNReal)⁻¹ ≤ r := by
    have ht : Tendsto (fun n : ℕ => c * (n : ENNReal)⁻¹) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hc)
    exact Filter.Tendsto.eventually_le_const hr ht
  have hpadding (i : Fin Q) : ∀ᶠ n : ℕ in atTop,
      (n : ENNReal)⁻¹ ≤ hatZeta i ∧
      (n : ENNReal)⁻¹ ≤ zeta i - hatZeta i ∧
      hatZeta i + 2 / (n : ENNReal) ≤ zeta i ∧
      hatZeta i + 1 / (zeta i * (n : ENNReal)) ≤ zeta i ∧
      omega (i + 1) + 2 / (n : ENNReal) ≤ epsilon (i + 1) ∧
      omega (i + 1) + 1 / (epsilon (i + 1) * (n : ENNReal)) ≤ epsilon (i + 1) := by
    obtain ⟨hh, hhz, hzfin, hoe, he1⟩ := hreserves i i.isLt
    have hz : 0 < zeta i := hh.trans hhz
    have he : 0 < epsilon (i + 1) := lt_of_le_of_lt bot_le hoe
    have hefin : epsilon (i + 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top he1
    have hr : 0 < zeta i - hatZeta i := tsub_pos_iff_lt.mpr hhz
    have hq : 0 < epsilon (i + 1) - omega (i + 1) := tsub_pos_iff_lt.mpr hoe
    filter_upwards [hsmall 1 _ (by norm_num) hh,
      hsmall 1 _ (by norm_num) hr, hsmall 2 _ (by norm_num) hr,
      hsmall (zeta i)⁻¹ _ (by simpa using hz.ne') hr,
      hsmall 2 _ (by norm_num) hq,
      hsmall (epsilon (i + 1))⁻¹ _ (by simpa using he.ne') hq]
      with n hinner hgap htwo hrow hout hnormalize
    simp only [one_mul] at hinner hgap
    have hroweq : 1 / (zeta i * (n : ENNReal)) = (zeta i)⁻¹ * (n : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.mul_inv (Or.inl hz.ne') (Or.inl hzfin)]
    have hnormeq : 1 / (epsilon (i + 1) * (n : ENNReal)) =
        (epsilon (i + 1))⁻¹ * (n : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.mul_inv (Or.inl he.ne') (Or.inl hefin)]
    refine ⟨hinner, hgap, ?_, ?_, ?_, ?_⟩
    · exact (ENNReal.le_sub_iff_add_le_left
        (ne_top_of_le_ne_top hzfin hhz.le) hhz.le).mp htwo
    · rw [hroweq]
      exact (ENNReal.le_sub_iff_add_le_left
        (ne_top_of_le_ne_top hzfin hhz.le) hhz.le).mp hrow
    · exact (ENNReal.le_sub_iff_add_le_left
        (ne_top_of_le_ne_top hefin hoe.le) hoe.le).mp hout
    · rw [hnormeq]
      exact (ENNReal.le_sub_iff_add_le_left
        (ne_top_of_le_ne_top hefin hoe.le) hoe.le).mp hnormalize
  have hdecay : ∀ᶠ n : ℕ in atTop,
      (Delta : ENNReal) * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹ := by
    have hb : 1 - a < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num) ha.ne'
    have ht : Tendsto (fun n : ℕ => (Delta : ENNReal) * (1 - a) ^ n)
        atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hb)
        (Or.inr (ENNReal.natCast_ne_top Delta))
    exact Filter.Tendsto.eventually_le_const (by norm_num) ht
  have hCbound : ∀ᶠ n : ℕ in atTop, C / (n : ENNReal) ≤ 1 := by
    simpa only [div_eq_mul_inv] using hsmall C 1 hCtop (by norm_num)
  have hall := Filter.eventually_all.mpr hpadding
  have horder : ∀ᶠ n : ℕ in atTop,
      C / (n : ENNReal) ≤ 1 ∧ Delta * (1 - a) ^ n ≤ (2 : ENNReal)⁻¹ ∧
      ∀ s, s < Q →
        (n : ENNReal)⁻¹ ≤ hatZeta s ∧
        (n : ENNReal)⁻¹ ≤ zeta s - hatZeta s ∧
        hatZeta s + 2 / (n : ENNReal) ≤ zeta s ∧
        hatZeta s + 1 / (zeta s * (n : ENNReal)) ≤ zeta s ∧
        omega (s + 1) + 2 / (n : ENNReal) ≤ epsilon (s + 1) ∧
        omega (s + 1) + 1 / (epsilon (s + 1) * (n : ENNReal)) ≤ epsilon (s + 1) := by
    filter_upwards [hCbound, hdecay, hall] with n hC hD hp
    exact ⟨hC, hD, fun s hs => hp ⟨s, hs⟩⟩
  obtain ⟨N, hN⟩ := horder.exists_forall_of_atTop
  refine ⟨a, M, C, max N Ncert, ha, ha1, hM, le_rfl, ?_, ?_⟩
  · intro s hs
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨hw, hh, hm, he, _⟩ := hNcert s x x hs hx hx
      exact ⟨haconst s x x hs hx hx, hMconst s x hs hx,
        hw.trans (le_max_right _ _), hh.trans (le_max_right _ _),
        hm.trans (le_max_right _ _), he.trans (le_max_right _ _)⟩
    · intro x y hx hy
      exact ⟨haconst s x y hs hx hy,
        (hNcert s x y hs hx hy).2.2.2.2.trans (le_max_right _ _)⟩
  · intro n hn
    exact hN n ((le_max_left _ _).trans hn)
