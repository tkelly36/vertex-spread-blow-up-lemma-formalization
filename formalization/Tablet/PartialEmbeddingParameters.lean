import Tablet.Preamble

open scoped NNReal

-- [TABLET NODE: PartialEmbeddingParameters]
theorem PartialEmbeddingParameters (Δ : ℕ) (d : ENNReal) (hd : 0 < d) (hd1 : d ≤ 1) :
    let a := d * (d / 2) ^ Δ
    ∃ d₀' : ENNReal, 0 < d₀' ∧ d₀' < d ∧
      ∀ d' : ENNReal, 0 < d' → d' ≤ d₀' →
        ∃ ε₀ : ENNReal, 0 < ε₀ ∧ ε₀ < ⊤ ∧
        ∀ ε : ENNReal, 0 < ε → ε ≤ ε₀ →
          ∃ C₀ : ENNReal, 1 ≤ C₀ ∧ C₀ < ⊤ ∧
          ∀ C : ENNReal, C₀ ≤ C → C < ⊤ →
            ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
              0 < n ∧ ε ≤ 1 / 2 ∧ ε ≤ d / 2 ∧
              0 < a ∧ a ≤ d ∧
              (∀ k : ℕ, k ≤ Δ → a ≤ d * (d - ε) ^ k) ∧
              ε * (1 + ε) < a ∧
              (Δ + 1 : ENNReal) * ε * (1 + ε) ≤ a / 2 ∧
              d' ≤ a / 4 ∧ 2 / a ≤ C ∧ 2 ≤ C ∧ C / n ≤ 1 ∧
              (∀ t : ℕ, a / 2 * n ≤ (t : ENNReal) → 1 / (t : ENNReal) ≤ C / n) ∧
              (∀ t : ℕ, (1 - ε) * n ≤ (t : ENNReal) →
                0 < t ∧ 1 / (t : ENNReal) ≤ C / n) := by
-- BODY
  lift d to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top hd1
  norm_cast at hd hd1
  let a : ℝ≥0 := d * (d / 2) ^ Δ
  have ha : 0 < a := by dsimp [a]; positivity
  have ha_d : a ≤ d := by
    have hhalf : d / 2 ≤ 1 := by rify at hd1 ⊢; linarith
    exact (mul_le_mul_right (pow_le_one₀ (zero_le _) hhalf) d).trans_eq (mul_one d)
  have ha1 : a ≤ 1 := ha_d.trans hd1
  have hquarter : a / 4 < d := by
    have h : a / 4 < a := by rify at ha ⊢; linarith
    exact h.trans_le ha_d
  refine ⟨↑(a / 4), by exact_mod_cast (show 0 < a / 4 by positivity),
    by simpa [a] using (ENNReal.coe_lt_coe.mpr hquarter), ?_⟩
  intro d' hd' hd'a
  lift d' to ℝ≥0 using ne_top_of_le_ne_top ENNReal.coe_ne_top hd'a
  norm_cast at hd' hd'a
  let e : ℝ≥0 := min (1 / 2) (min (d / 2) (min (d' / 4) (a / (8 * (Δ + 1)))))
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨↑e, by exact_mod_cast he, ENNReal.coe_lt_top, ?_⟩
  intro ε hε hεe
  lift ε to ℝ≥0 using ne_top_of_le_ne_top ENNReal.coe_ne_top hεe
  norm_cast at hε hεe
  obtain ⟨hεhalf, hεd, hεd', hεa⟩ :
      ε ≤ 1 / 2 ∧ ε ≤ d / 2 ∧ ε ≤ d' / 4 ∧ ε ≤ a / (8 * (Δ + 1)) := by
    simpa only [e, le_min_iff] using hεe
  have hloss : (Δ + 1 : ℝ≥0) * ε ≤ a / 8 := by
    have h := (le_div_iff₀ (show (0 : ℝ≥0) < 8 * (Δ + 1) by positivity)).mp hεa
    rify at h ⊢
    nlinarith only [h]
  have hepsLoss : ε ≤ a / 8 := by
    have hD1 : (1 : ℝ≥0) ≤ Δ + 1 := by simp
    exact (le_mul_of_one_le_left (zero_le ε) hD1).trans hloss
  have hstrict : ε * (1 + ε) < a := by
    rify at hεhalf hepsLoss ha ⊢
    have hprod := mul_le_mul hepsLoss (show (1 : ℝ) + ε ≤ 3 / 2 by linarith)
      (by positivity : (0 : ℝ) ≤ 1 + ε) (by positivity : (0 : ℝ) ≤ (a : ℝ) / 8)
    nlinarith only [hprod, ha]
  have htotal : (Δ + 1 : ℝ≥0) * ε * (1 + ε) ≤ a / 2 := by
    rify at hεhalf hloss ⊢
    have hprod := mul_le_mul hloss (show (1 : ℝ) + ε ≤ 3 / 2 by linarith)
      (by positivity : (0 : ℝ) ≤ 1 + ε) (by positivity : (0 : ℝ) ≤ (a : ℝ) / 8)
    nlinarith only [hprod, a.coe_nonneg]
  have hpower : ∀ k : ℕ, k ≤ Δ → a ≤ d * (d - ε) ^ k := by
    intro k hk
    have hbase : d / 2 ≤ d - ε := by
      exact le_tsub_of_add_le_left (by rify at hεd ⊢; linarith)
    have hhalf : d / 2 ≤ 1 := by rify at hd1 ⊢; linarith
    exact mul_le_mul_right ((pow_le_pow_of_le_one (zero_le _) hhalf hk).trans
      (pow_le_pow_left₀ (zero_le _) hbase k)) d
  let c : ℝ≥0 := max 1 (max (2 / a) (max (2 / d') (1 / ε)))
  have hc1 : 1 ≤ c := le_max_left _ _
  have hca : 2 / a ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have htwo : 2 ≤ 2 / a := (le_div_iff₀ ha).mpr (by simpa using mul_le_mul_right ha1 2)
  refine ⟨↑c, by exact_mod_cast hc1, ENNReal.coe_lt_top, ?_⟩
  intro C hC hCtop
  lift C to ℝ≥0 using hCtop.ne
  norm_cast at hC
  have hCa : 2 / a ≤ C := hca.trans hC
  have hC2 : 2 ≤ C := htwo.trans hCa
  obtain ⟨m, hm⟩ := exists_nat_ge C
  refine ⟨max 1 m, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  have hnN : (0 : ℝ≥0) < n := by exact_mod_cast hnpos
  have hCn : C ≤ n := hm.trans (by exact_mod_cast ((le_max_right 1 m).trans hn))
  have hlegal : ∀ t : ℕ, a / 2 * n ≤ (t : ℝ≥0) →
      1 / (t : ℝ≥0) ≤ C / n := by
    intro t ht
    have htN : (0 : ℝ≥0) < t := lt_of_lt_of_le (by positivity) ht
    have hCan : 2 ≤ C * a := (div_le_iff₀ ha).mp hCa
    have hmult : (n : ℝ≥0) ≤ C * t := by
      have h := mul_le_mul_right ht C
      rify at h hCan ⊢
      have h' := mul_le_mul_of_nonneg_right hCan (show (0 : ℝ) ≤ n by positivity)
      nlinarith only [h, h']
    exact (div_le_div_iff₀ htN hnN).mpr (by simpa using hmult)
  have hfallback : ∀ t : ℕ, (1 - ε) * n ≤ (t : ℝ≥0) →
      0 < t ∧ 1 / (t : ℝ≥0) ≤ C / n := by
    intro t ht
    have hhalf : (1 / 2 : ℝ≥0) ≤ 1 - ε :=
      le_tsub_of_add_le_left (by rify at hεhalf ⊢; linarith)
    have htHalf : (n : ℝ≥0) / 2 ≤ t := by
      simpa [div_eq_mul_inv, mul_comm] using (mul_le_mul_left hhalf (n : ℝ≥0)).trans ht
    have htN : (0 : ℝ≥0) < t := lt_of_lt_of_le (by positivity) htHalf
    have htpos : 0 < t := by exact_mod_cast htN
    refine ⟨htpos, (div_le_div_iff₀ htN hnN).mpr ?_⟩
    have hmult := mul_le_mul_left hC2 (t : ℝ≥0)
    rify at htHalf hmult ⊢
    nlinarith only [htHalf, hmult]
  have haE : (↑a : ENNReal) = (↑d : ENNReal) * (↑d / 2) ^ Δ := by
    norm_cast
  change 0 < n ∧ _
  rw [← haE]
  refine ⟨hnpos, ?_, by exact_mod_cast hεd,
    by exact_mod_cast ha, by exact_mod_cast ha_d, ?_,
    by exact_mod_cast hstrict, by exact_mod_cast htotal, by exact_mod_cast hd'a,
    ?_, by exact_mod_cast hC2, ?_, ?_, ?_⟩
  · simpa only [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat] using ENNReal.coe_le_coe.mpr hεhalf
  · intro k hk
    exact_mod_cast hpower k hk
  · simpa only [ENNReal.coe_div ha.ne', ENNReal.coe_ofNat] using
      ENNReal.coe_le_coe.mpr hCa
  · change (↑C : ENNReal) / (↑(n : ℝ≥0)) ≤ 1
    rw [← ENNReal.coe_div (p := C) hnN.ne']
    exact_mod_cast ((div_le_one₀ hnN).mpr hCn)
  · intro t ht
    have ht' : a / 2 * n ≤ (t : ℝ≥0) := by exact_mod_cast ht
    have htN : (0 : ℝ≥0) < t := lt_of_lt_of_le (by positivity) ht'
    change (↑(1 : ℝ≥0) : ENNReal) / ↑(t : ℝ≥0) ≤ (↑C : ENNReal) / ↑(n : ℝ≥0)
    rw [← ENNReal.coe_div (p := 1) htN.ne', ← ENNReal.coe_div (p := C) hnN.ne']
    exact_mod_cast hlegal t ht'
  · intro t ht
    have ht' : (1 - ε) * n ≤ (t : ℝ≥0) := by exact_mod_cast ht
    obtain ⟨htpos, hbound⟩ := hfallback t ht'
    have htN : (0 : ℝ≥0) < t := by exact_mod_cast htpos
    refine ⟨htpos, ?_⟩
    change (↑(1 : ℝ≥0) : ENNReal) / ↑(t : ℝ≥0) ≤ (↑C : ENNReal) / ↑(n : ℝ≥0)
    rw [← ENNReal.coe_div (p := 1) htN.ne', ← ENNReal.coe_div (p := C) hnN.ne']
    exact_mod_cast hbound
