import Tablet.InductionApplicationCertificate
import Tablet.NearEqualFourGraphs
import Tablet.UniformPerfectMatchingSpread
import Tablet.QuantitativeSuperRegularThinning
import Tablet.MatchingEnumeration

-- [TABLET NODE: EqualSizeOneRoundChoices]
theorem EqualSizeOneRoundChoices (d : ENNReal) (Delta : ℕ)
    (p rho : ℕ → ENNReal) (e : ENNReal)
    (hd : 0 < d) (hd1 : d ≤ 1) (he : 0 < e) (he1 : e ≤ 1)
    (hdens : ∀ x, x ≤ Delta →
      0 < p x ∧ p x ≤ 1 ∧ 0 < rho x ∧ rho x < p x)
    (hgaps : ∀ y, y < Delta → 0 < p y - p (y + 1)) :
    ∃ (omega theta zeta hatZeta b : ENNReal)
      (K : InductionApplicationCertificate Delta 1 d
        (fun _ => theta) p (fun _ => b) rho (fun _ => zeta)
        (fun _ => omega) (fun _ => hatZeta)),
      0 < b ∧ b < hatZeta ∧ hatZeta < zeta ∧
      0 < theta ∧ 0 < omega ∧ omega < e ∧ b ≤ e ∧
      2 * zeta ^ (2 : ℝ)⁻¹ ≤ theta ∧
      zeta + Delta * zeta ^ (2 : ℝ)⁻¹ ≤ theta ∧
      zeta + 2 * Delta * zeta ≤ theta ∧
      (∀ x, x ≤ Delta →
        4 * theta < rho x ∧ 2 * zeta < rho x ∧ 2 * zeta < 1 - rho x) ∧
      2 * zeta < d / 2 ∧ 2 * zeta < 1 - d / 2 ∧
      (∀ y, y < Delta → 2 * b < p y - p (y + 1)) ∧
      (∀ x, x ≤ Delta → K.matchingConstant 0 x ≠ ⊤) := by
-- BODY
  classical
  -- An anchored finite minimum also works for empty indexing types and top caps.
  have small {I : Type} [Fintype I] (c : ENNReal) (hc : 0 < c)
      (f : I → ENNReal) (hf : ∀ i, 0 < f i) :
      ∃ a : ENNReal, 0 < a ∧ a < c ∧ a < 1 ∧ ∀ i, a < f i := by
    let v := min c (min 1 (Finset.univ.inf f))
    have hv : 0 < v := lt_min hc (lt_min (by norm_num)
      ((Finset.lt_inf_iff (by simp : (0 : ENNReal) < ⊤)).mpr (fun i _ => hf i)))
    have hv1 : v ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hav : v / 2 < v := ENNReal.half_lt_self hv.ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top hv1)
    refine ⟨v / 2, ENNReal.div_pos hv.ne' (by norm_num),
      hav.trans_le (min_le_left _ _), hav.trans_le hv1, ?_⟩
    intro i
    exact hav.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (Finset.inf_le (Finset.mem_univ i))))
  let X := Fin (Delta + 1)
  have hx (i : X) : (i : ℕ) ≤ Delta := by have := i.isLt; omega
  have hp (i : X) := hdens i (hx i)
  have hr (i : X) : rho i < 1 := (hp i).2.2.2.trans_le (hp i).2.1
  have hrtop (i : X) : rho i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hr i).le
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd1
  have hhalf : 0 < d / 2 := ENNReal.div_pos hd.ne' (by norm_num)
  have hhalf1 : d / 2 < 1 := by
    calc
      d / 2 ≤ 1 / 2 := by gcongr
      _ < 1 := by norm_num
  have hc (i : X × X) := NearEqualFourGraphs (rho i.1) (rho i.2) (d / 2)
    (hp i.1).2.2.1 (hr i.1).le (hp i.2).2.2.1 (hr i.2).le hhalf hhalf1.le
  choose outCap houtCap houtput using hc
  obtain ⟨omega, homega, homegae, homega1, homegaCap⟩ := small e he outCap houtCap
  have hinputs (i : X × X) := houtput i omega homega (homegaCap i).le
  choose inCap hinCap hinput using hinputs
  obtain ⟨theta, htheta, _, htheta1, hthetaCap⟩ := small 1 (by norm_num)
    (fun i : X × X => min (inCap i) (rho i.1 / 8))
    (fun i => lt_min (hinCap i) (ENNReal.div_pos (hp i.1).2.2.1.ne' (by norm_num)))
  have hthetaIn (i : X × X) : theta ≤ inCap i :=
    (hthetaCap i).le.trans (min_le_left _ _)
  have hthetaRho (i : X) : 4 * theta < rho i := by
    as_aux_lemma =>
    have ht : theta < rho i / 8 := (hthetaCap (i, i)).trans_le (min_le_right _ _)
    have htf : theta ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top htheta1.le
    have htr := (ENNReal.toReal_lt_toReal htf
      (ENNReal.div_ne_top (hrtop i) (by norm_num))).mpr ht
    apply (ENNReal.toReal_lt_toReal (by finiteness) (hrtop i)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] at *
    have hrr := ENNReal.toReal_pos (hp i).2.2.1.ne' (hrtop i)
    nlinarith only [htr, hrr]
  have hexp (i : X × X) := hinput i theta htheta (hthetaIn i)
  choose expCap hexpCap hexponential using hexp
  have ha (i : X × X) := small (expCap i) (hexpCap i)
    (fun _ : Fin 0 => (1 : ENNReal)) (fun _ => by norm_num)
  choose a hapos haCap ha1 haunused using ha
  have hfour (i : X × X) := hexponential i (a i) (hapos i) (haCap i).le
  choose fourN hfourGuarantee using hfour
  have hspread (i : X) := UniformPerfectMatchingSpread theta (rho i)
    htheta (hthetaRho i) (hr i).le
  choose M hM hMtop matchN hmatch using hspread
  have htwo (i : X) : 2 * theta < rho i :=
    (mul_le_mul_left (by norm_num : (2 : ENNReal) ≤ 4) theta).trans_lt (hthetaRho i)
  have hcount (i : X) := MatchingEnumeration theta (rho i) htheta (htwo i) (hr i).le
  choose existN hexist using hcount
  have hthetatop : theta ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top htheta1.le
  have hhalfTop : d / 2 ≠ ⊤ := by finiteness
  have hhalfD : d / 2 < d := ENNReal.half_lt_self hd.ne' hdtop
  have hcomp (i : X) : 0 < 1 - rho i := tsub_pos_iff_lt.mpr (hr i)
  have hhostcomp : 0 < 1 - d / 2 := tsub_pos_iff_lt.mpr hhalf1
  let cap := min (theta / (2 * (Delta + 1)))
    (min (theta / (1 + 2 * Delta)) (min ((d / 2) / 20) ((1 - d / 2) / 4)))
  have hcap : 0 < cap := by
    dsimp [cap]
    refine lt_min (ENNReal.div_pos htheta.ne' (by finiteness))
      (lt_min (ENNReal.div_pos htheta.ne' (by finiteness))
      (lt_min (ENNReal.div_pos hhalf.ne' (by norm_num))
        (ENNReal.div_pos hhostcomp.ne' (by norm_num))))
  obtain ⟨h, hh, hhcap, hh1, hhx⟩ := small cap hcap
    (fun i : X => min (rho i / 20) ((1 - rho i) / 4))
    (fun i => lt_min (ENNReal.div_pos (hp i).2.2.1.ne' (by norm_num))
      (ENNReal.div_pos (hcomp i).ne' (by norm_num)))
  have hhtop : h ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hh1.le
  have hhA : h < theta / (2 * (Delta + 1)) := hhcap.trans_le (min_le_left _ _)
  have hhB : h < theta / (1 + 2 * Delta) :=
    hhcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhD : h < (d / 2) / 20 := hhcap.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhDc : h < (1 - d / 2) / 4 := hhcap.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hhR (i : X) : h < rho i / 20 := (hhx i).trans_le (min_le_left _ _)
  have hhRc (i : X) : h < (1 - rho i) / 4 := (hhx i).trans_le (min_le_right _ _)
  let zeta := h ^ 2
  let hatZeta := zeta / 2
  have hzetapos : 0 < zeta := ENNReal.pow_pos hh 2
  have hzetatop : zeta ≠ ⊤ := by dsimp [zeta]; finiteness
  have hhatpos : 0 < hatZeta := ENNReal.div_pos hzetapos.ne' (by norm_num)
  have hhattop : hatZeta ≠ ⊤ := by dsimp [hatZeta]; finiteness
  have hhatlt : hatZeta < zeta := ENNReal.half_lt_self hzetapos.ne' hzetatop
  have hzle : zeta ≤ h := by
    dsimp [zeta]
    rw [pow_two]
    simpa using mul_le_mul_right hh1.le h
  have hroot : zeta ^ (2 : ℝ)⁻¹ = h :=
    ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) h
  -- All arithmetic below is in the finite real part of ENNReal.
  have hRpos : 0 < h.toReal := ENNReal.toReal_pos hh.ne' hhtop
  have hR1 : h.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hhtop ENNReal.one_ne_top).mpr hh1
  have hRA : h.toReal < theta.toReal / (2 * ((Delta : ℝ) + 1)) := by
    have H := (ENNReal.toReal_lt_toReal hhtop (by finiteness)).mpr hhA
    simpa using H
  have hRB : h.toReal < theta.toReal / (1 + 2 * (Delta : ℝ)) := by
    have H := (ENNReal.toReal_lt_toReal hhtop (by finiteness)).mpr hhB
    simpa using H
  have hthetaR : 0 < theta.toReal := ENNReal.toReal_pos htheta.ne' hthetatop
  have hAp : 0 < 2 * ((Delta : ℝ) + 1) := by positivity
  have hBp : 0 < 1 + 2 * (Delta : ℝ) := by positivity
  have hAmul := (lt_div_iff₀ hAp).mp hRA
  have hBmul := (lt_div_iff₀ hBp).mp hRB
  have hrootBudget : 2 * zeta ^ (2 : ℝ)⁻¹ ≤ theta := by
    as_aux_lemma =>
    rw [hroot]
    apply (ENNReal.toReal_le_toReal (by finiteness) hthetatop).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    have hD0 : (0 : ℝ) ≤ Delta := Nat.cast_nonneg _
    nlinarith only [hAmul, hRpos, hD0]
  have hsumBudget : zeta + Delta * zeta ^ (2 : ℝ)⁻¹ ≤ theta := by
    as_aux_lemma =>
    rw [hroot]
    apply (ENNReal.toReal_le_toReal (by finiteness) hthetatop).mp
    rw [ENNReal.toReal_add hzetatop (by finiteness)]
    simp only [zeta, ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hD0 : (0 : ℝ) ≤ Delta := Nat.cast_nonneg _
    have hs : h.toReal ^ 2 ≤ h.toReal := by nlinarith
    nlinarith only [hAmul, hRpos, hD0, hs]
  have hlinearBudget : zeta + 2 * Delta * zeta ≤ theta := by
    as_aux_lemma =>
    apply (ENNReal.toReal_le_toReal (by finiteness) hthetatop).mp
    rw [ENNReal.toReal_add hzetatop (by finiteness)]
    simp only [zeta, ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    have hD0 : (0 : ℝ) ≤ Delta := Nat.cast_nonneg _
    have hs : h.toReal ^ 2 ≤ h.toReal := by nlinarith
    have H := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 + 2 * (Delta : ℝ))
    nlinarith only [hBmul, H]
  have hsmallR (i : X) : 2 * zeta < rho i ∧
      2 * zeta < 1 - rho i ∧ 10 * hatZeta < rho i := by
    as_aux_lemma =>
    have H := (ENNReal.toReal_lt_toReal hhtop
      (ENNReal.div_ne_top (hrtop i) (by norm_num))).mpr (hhR i)
    have J := (ENNReal.toReal_lt_toReal hhtop (by finiteness)).mpr (hhRc i)
    simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at H J
    have hs : h.toReal ^ 2 ≤ h.toReal := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · apply (ENNReal.toReal_lt_toReal (by finiteness) (hrtop i)).mp
      simp only [zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
      nlinarith only [H, hs, hRpos]
    · apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simp only [zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
      nlinarith only [J, hs, hRpos]
    · apply (ENNReal.toReal_lt_toReal (by finiteness) (hrtop i)).mp
      simp only [hatZeta, zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_div, ENNReal.toReal_pow]
      nlinarith only [H, hs, hRpos]
  have hsmallD : 2 * zeta < d / 2 ∧ 2 * zeta < 1 - d / 2 ∧
      10 * hatZeta < d / 2 := by
    as_aux_lemma =>
    have H := (ENNReal.toReal_lt_toReal hhtop (by finiteness)).mpr hhD
    have J := (ENNReal.toReal_lt_toReal hhtop (by finiteness)).mpr hhDc
    simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at H J
    have hs : h.toReal ^ 2 ≤ h.toReal := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · apply (ENNReal.toReal_lt_toReal (by finiteness) hhalfTop).mp
      simp only [zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_pow, ENNReal.toReal_div]
      nlinarith only [H, hs, hRpos]
    · apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simp only [zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow]
      nlinarith only [J, hs, hRpos]
    · apply (ENNReal.toReal_lt_toReal (by finiteness) hhalfTop).mp
      simp only [hatZeta, zeta, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
        ENNReal.toReal_div, ENNReal.toReal_pow]
      nlinarith only [H, hs, hRpos]
  obtain ⟨b, hb, hbcap, hb1, hbgap⟩ := small (min e (hatZeta / 16))
    (lt_min he (ENNReal.div_pos hhatpos.ne' (by norm_num)))
    (fun i : Fin Delta => (p i - p (i + 1)) / 4)
    (fun i => ENNReal.div_pos (hgaps i i.isLt).ne' (by norm_num))
  have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb1.le
  have hbe : b ≤ e := hbcap.le.trans (min_le_left _ _)
  have hb16 : b ≤ hatZeta / 16 := hbcap.le.trans (min_le_right _ _)
  have hbhat : b < hatZeta := by
    apply (hbcap.trans_le (min_le_right _ _)).trans_le
    calc
      hatZeta / 16 ≤ hatZeta * 1 := by
        change hatZeta * (16 : ENNReal)⁻¹ ≤ hatZeta * 1
        gcongr
        norm_num
      _ = hatZeta := mul_one _
  have hgap (y : ℕ) (hy : y < Delta) : 2 * b < p y - p (y + 1) := by
    as_aux_lemma =>
    have H := hbgap ⟨y, hy⟩
    have hg : p y - p (y + 1) ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      exact tsub_le_self.trans (hdens y (by omega)).2.1
    have H' := (ENNReal.toReal_lt_toReal hbtop (by finiteness)).mpr H
    apply (ENNReal.toReal_lt_toReal (by finiteness) hg).mp
    simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at *
    have hp' := ENNReal.toReal_pos (hgaps y hy).ne' hg
    nlinarith only [H', hp']
  let xi := hatZeta / 16
  have hxi : 0 < xi := ENNReal.div_pos hhatpos.ne' (by norm_num)
  have hbudget (D r : ENNReal) (hD : 0 < D) (hDt : D ≠ ⊤) (hrD : r ≤ D) :
      4 * ((r / D) * b + xi) ≤ hatZeta := by
    as_aux_lemma =>
    have hratio : r / D ≤ 1 := (ENNReal.div_le_iff hD.ne' hDt).mpr (by simpa using hrD)
    have H : 4 * (b + xi) ≤ hatZeta := by
      apply (ENNReal.toReal_le_toReal (by dsimp [xi]; finiteness) hhattop).mp
      have hbR := (ENNReal.toReal_le_toReal
        hbtop (by finiteness)).mpr hb16
      rw [ENNReal.toReal_mul, ENNReal.toReal_add
        hbtop (by dsimp [xi]; finiteness)]
      simp only [xi, ENNReal.toReal_ofNat, ENNReal.toReal_div] at *
      have hhat0 : 0 ≤ hatZeta.toReal := ENNReal.toReal_nonneg
      linarith only [hbR, hhat0]
    apply le_trans _ H
    gcongr
    simpa using mul_le_mul_left hratio b
  have hwitness (i : X) := QuantitativeSuperRegularThinning b (p i) (rho i) hatZeta xi
    hb hbhat (hp i).2.2.1 (hp i).2.2.2 (hp i).2.1 hxi
    (hbudget (p i) (rho i) (hp i).1
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hp i).2.1) (hp i).2.2.2.le)
    (hsmallR i).2.2
  choose witnessN hwitnessGuarantee using hwitness
  obtain ⟨hostN, hhostGuarantee⟩ := QuantitativeSuperRegularThinning b d (d / 2) hatZeta xi
    hb hbhat hhalf hhalfD hd1 hxi (hbudget d (d / 2) hd hdtop hhalfD.le) hsmallD.2.2
  let extN (f : X → ℕ) (x : ℕ) := if H : x ≤ Delta then f ⟨x, by omega⟩ else 0
  let extC (f : X → ENNReal) (x : ℕ) :=
    if H : x ≤ Delta then f ⟨x, by omega⟩ else 1
  let extPairN (f : X × X → ℕ) (x y : ℕ) :=
    if H : x ≤ Delta ∧ y ≤ Delta then f (⟨x, by omega⟩, ⟨y, by omega⟩) else 0
  let extPairC (f : X × X → ENNReal) (x y : ℕ) :=
    if H : x ≤ Delta ∧ y ≤ Delta then f (⟨x, by omega⟩, ⟨y, by omega⟩) else 1 / 2
  let K : InductionApplicationCertificate Delta 1 d
      (fun _ => theta) p (fun _ => b) rho (fun _ => zeta)
      (fun _ => omega) (fun _ => hatZeta) := {
    witnessThinningThreshold := fun round x => if round = 0 then extN witnessN x else 0
    hostThinningThreshold := fun round => if round = 0 then hostN else 0
    fourGraphsConstant := fun round x y => if round = 0 then extPairC a x y else 1 / 2
    fourGraphsThreshold := fun round x y => if round = 0 then extPairN fourN x y else 0
    matchingConstant := fun round x => if round = 0 then extC M x else 1
    matchingThreshold := fun round x => if round = 0 then extN matchN x else 0
    matchingExistenceThreshold := fun round x => if round = 0 then extN existN x else 0
    witnessThinningGuarantee := by
      intro round hround x hx V _ _ G _ L R hLR hL hR hnearL hnearR hG
      have hr0 : round = 0 := by omega
      subst round
      simp only [extN, dif_pos hx] at hL hR
      exact hwitnessGuarantee ⟨x, by omega⟩ G L R hLR hL hR hnearL hnearR hG
    hostThinningGuarantee := by
      intro round hround V _ _ G _ L R hLR hL hR hnearL hnearR hG
      have hr0 : round = 0 := by omega
      subst round
      exact hhostGuarantee G L R hLR hL hR hnearL hnearR hG
    fourGraphsPositive := by
      intro round hround x y hx hy
      have hr0 : round = 0 := by omega
      subst round
      simp only [extPairC, dif_pos (And.intro hx hy)]
      exact ⟨hapos (⟨x, by omega⟩, ⟨y, by omega⟩),
        (ha1 (⟨x, by omega⟩, ⟨y, by omega⟩)).le⟩
    fourGraphsGuarantee := by
      intro round hround x y hx hy V _ _ F₁₂ F₁₃ F₂₃ _ _ _ W₁ W₂ W₃ m hm ht h₁₂ hM
      have hr0 : round = 0 := by omega
      subst round
      simp only [extPairN, dif_pos (And.intro hx hy)] at hm
      simp only [extPairC, dif_pos (And.intro hx hy)]
      exact hfourGuarantee (⟨x, by omega⟩, ⟨y, by omega⟩)
        F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ m hm ht h₁₂ hM
    matchingConstantAtLeastOne := by
      intro round hround x hx
      have hr0 : round = 0 := by omega
      subst round
      simp only [extC, dif_pos hx]
      exact hM ⟨x, by omega⟩
    matchingExistenceGuarantee := by
      intro round hround x hx V _ _ G _ U W hUW m hm hU hW hG
      have hr0 : round = 0 := by omega
      subst round
      simp only [extN, dif_pos hx] at hm
      have H := hexist ⟨x, by omega⟩ G U W hUW m hm hU hW hG
      have hbase : 0 < rho x - 2 * theta := tsub_pos_iff_lt.mpr (htwo ⟨x, by omega⟩)
      have hpositive : 0 < (rho x - 2 * theta) ^ m * (m.factorial : ENNReal) :=
        ENNReal.mul_pos (ENNReal.pow_pos hbase m).ne'
          (by exact_mod_cast (Nat.factorial_pos m).ne')
      have hcard : 0 < ({f : U → W | PerfectMatching G U W hUW f}.ncard : ENNReal) :=
        hpositive.trans_le H
      have hnat : 0 < {f : U → W | PerfectMatching G U W hUW f}.ncard := by
        exact_mod_cast hcard
      obtain ⟨f, hf⟩ := Set.nonempty_of_ncard_ne_zero hnat.ne'
      exact ⟨⟨f, hf⟩⟩
    matchingGuarantee := by
      intro round hround x hx V _ _ G _ U W hUW m hm hU hW hG hnonempty
      have hr0 : round = 0 := by omega
      subst round
      simp only [extN, dif_pos hx] at hm
      simp only [extC, dif_pos hx]
      have H := hmatch ⟨x, by omega⟩ G U W hUW m hm hU hW hG hnonempty
      let mu := (UniformPerfectMatching G U W hUW hnonempty).map Subtype.val
      let inclusion (f : U → W) (u : U) : V := (f u : V)
      have hlaw :
          (UniformPerfectMatching G U W hUW hnonempty).map (fun f u => (f.val u : V)) =
            mu.map inclusion := by
        rw [PMF.map_comp]
        rfl
      rw [hlaw]
      refine ⟨H.1, ?_⟩
      intro s xx yy hinj _
      rw [PMF.toOuterMeasure_map_apply]
      by_cases hy : ∀ i, yy i ∈ W
      · let yr (i : Fin s) : W := ⟨yy i, hy i⟩
        have hevent : inclusion ⁻¹' CylinderEvent xx yy = CylinderEvent xx yr := by
          ext f
          constructor
          · intro hf i
            exact Subtype.ext (hf i)
          · intro hf i
            exact congrArg Subtype.val (hf i)
        rw [hevent]
        exact H.2 s xx yr hinj (fun _ => Set.mem_univ _)
      · have hevent : inclusion ⁻¹' CylinderEvent xx yy = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro f hf
          apply hy
          intro i
          have hi : (f (xx i) : V) = yy i := hf i
          rw [← hi]
          exact (f (xx i)).property
        rw [hevent]
        simp
  }
  refine ⟨omega, theta, zeta, hatZeta, b, K, hb, hbhat, hhatlt,
    htheta, homega, homegae, hbe, hrootBudget, hsumBudget, hlinearBudget,
    ?_, hsmallD.1, hsmallD.2.1, hgap, ?_⟩
  · intro x hx
    exact ⟨hthetaRho ⟨x, by omega⟩, (hsmallR ⟨x, by omega⟩).1,
      (hsmallR ⟨x, by omega⟩).2.1⟩
  · intro x hx
    simp only [K, extC, dif_pos hx]
    exact hMtop ⟨x, by omega⟩
