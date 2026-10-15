import Tablet.UniformPerfectMatching
import Tablet.SuperRegularPair
import Tablet.CylinderEvent
import Tablet.MatchingThreeEdgeSwitchValid
import Tablet.MatchingThreeEdgeSwitchInjective
import Tablet.MatchingThreeEdgeSwitchIncoming
import Tablet.MatchingSwitchCandidateCount
import Mathlib.Tactic.Linarith

-- [TABLET NODE: MatchingSwitching]
theorem MatchingSwitching :
    ∀ ε d : ENNReal, 0 < ε → 4 * ε < d → d ≤ 1 →
      ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V]
        [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (U W : Finset V) (hUW : Disjoint U W) (n : ℕ),
        n₀ ≤ n → U.card = n → W.card = n → SuperRegularPair G U W ε d →
        ∀ (h : Nonempty {f : U → W // PerfectMatching G U W hUW f})
          (k : ℕ) (xN : Fin k → U) (yN : Fin k → W),
          Function.Injective xN → Function.Injective yN →
          (∀ i, G.Adj (xN i) (yN i)) →
          (k : ENNReal) ≤ d * n / 2 → ∀ (x : U) (y : W),
          x ∉ Set.range xN → y ∉ Set.range yN → G.Adj x y →
          let μ := (UniformPerfectMatching G U W hUW h).map Subtype.val
          μ.toOuterMeasure
                (CylinderEvent xN yN ∩ CylinderEvent (fun _ : Fin 1 => x) (fun _ => y)) /
              μ.toOuterMeasure (CylinderEvent xN yN) ≤ C / n := by
-- BODY
  classical
  intro ε d hε h4 hd
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd
  have hεd : ε < d := lt_of_le_of_lt (by
    calc
      ε = 1 * ε := (one_mul ε).symm
      _ ≤ 4 * ε := mul_le_mul_right' (by norm_num) ε) h4
  have hεtop : ε ≠ ⊤ := ne_top_of_lt (hεd.trans_le hd)
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have h4r : 4 * ε.toReal < d.toReal := by
    have h := (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by norm_num) hεtop) hdtop).2 h4
    simpa using h
  let c : ℝ := (d.toReal - ε.toReal) * (d.toReal / 2 - ε.toReal) ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    have h₁ : 0 < d.toReal - ε.toReal := by linarith
    have h₂ : 0 < d.toReal / 2 - ε.toReal := by linarith
    positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (6 / c)
  let C : ENNReal := ENNReal.ofReal (max 1 (2 / c))
  refine ⟨C, ?_, ENNReal.ofReal_ne_top, m + 1, ?_⟩
  · simpa [C] using ENNReal.ofReal_le_ofReal (le_max_left 1 (2 / c))
  intro V _ _ G _ U W hUW n hn hU hW hSR h k xN yN hxinj hyinj hNadj hk
    x y hxN hyN hxyAdj
  have hnpos : 0 < n := by omega
  have hmn : (m : ℝ) < n := by exact_mod_cast (show m < n by omega)
  have h6n : 6 ≤ c * (n : ℝ) := by
    have ht := (div_lt_iff₀ hc).1 (hm.trans hmn)
    nlinarith
  -- The order threshold absorbs all three classes of degenerate candidates.
  have hdegenerate : 3 * (n : ℝ) ≤ (c / 2) * (n : ℝ) ^ 2 := by
    have ht := mul_nonneg (sub_nonneg.mpr h6n) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  let μ := (UniformPerfectMatching G U W hUW h).map Subtype.val
  change μ.toOuterMeasure
      (CylinderEvent xN yN ∩ CylinderEvent (fun _ : Fin 1 => x) (fun _ => y)) /
      μ.toOuterMeasure (CylinderEvent xN yN) ≤ C / n
  by_cases hzero : μ.toOuterMeasure (CylinderEvent xN yN) = 0
  · -- An empty conditioning event also makes its subevent empty in measure.
    have hnum : μ.toOuterMeasure
        (CylinderEvent xN yN ∩ CylinderEvent (fun _ : Fin 1 => x) (fun _ => y)) = 0 :=
      le_antisymm (hzero ▸ μ.toOuterMeasure.mono Set.inter_subset_left) bot_le
    simp [hnum, hzero]
  let Min := {f : U → W // PerfectMatching G U W hUW f ∧
    (∀ i, f (xN i) = yN i) ∧ f x = y}
  let Mout := {f : U → W // PerfectMatching G U W hUW f ∧
    (∀ i, f (xN i) = yN i) ∧ f x ≠ y}
  let Candidates (f : Min) := {p : U × U //
    x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2 ∧
    G.Adj x (f.val p.1) ∧ G.Adj p.1 (f.val p.2) ∧ G.Adj p.2 (f.val x) ∧
    p.1 ∉ Set.range xN ∧ p.2 ∉ Set.range xN}
  have switch_out (f : Min) (p : Candidates f) :
      PerfectMatching G U W hUW (MatchingThreeEdgeSwitch f.val x p.val.1 p.val.2) ∧
      (∀ i, MatchingThreeEdgeSwitch f.val x p.val.1 p.val.2 (xN i) = yN i) ∧
      MatchingThreeEdgeSwitch f.val x p.val.1 p.val.2 x ≠ y := by
    rcases p.property with ⟨hxa, hxb, hab, h₁, h₂, h₃, haN, hbN⟩
    exact MatchingThreeEdgeSwitchValid G U W hUW f.val f.property.1
      x p.val.1 p.val.2 y f.property.2.2 hxa hxb hab h₁ h₂ h₃
      xN yN f.property.2.1 (fun i hi => hxN ⟨i, hi⟩)
      (fun i hi => haN ⟨i, hi⟩) (fun i hi => hbN ⟨i, hi⟩)
  let switchMap (f : Min) (p : Candidates f) : Mout :=
    ⟨MatchingThreeEdgeSwitch f.val x p.val.1 p.val.2, switch_out f p⟩
  have switchMap_injective (f : Min) : Function.Injective (switchMap f) := by
    intro p q hpq
    have hfun : MatchingThreeEdgeSwitch f.val x p.val.1 p.val.2 =
        MatchingThreeEdgeSwitch f.val x q.val.1 q.val.2 := congrArg Subtype.val hpq
    have heq := MatchingThreeEdgeSwitchInjective f.val f.property.1.1 x
      (a₁ := ⟨p.val, p.property.1, p.property.2.1, p.property.2.2.1⟩)
      (a₂ := ⟨q.val, q.property.1, q.property.2.1, q.property.2.2.1⟩) hfun
    have hpqval : p.val = q.val := congrArg
      (fun r : {p : U × U // x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2} => r.val) heq
    exact Subtype.ext hpqval
  have incoming_unique (g : Mout) (f₁ f₂ : Min)
      (p : Candidates f₁) (q : Candidates f₂)
      (hp : switchMap f₁ p = g) (hq : switchMap f₂ q = g)
      (ha : p.val.1 = q.val.1) : f₁ = f₂ := by
    have hs₁ : MatchingThreeEdgeSwitch f₁.val x p.val.1 p.val.2 = g.val :=
      congrArg Subtype.val hp
    have hs₂ : MatchingThreeEdgeSwitch f₂.val x p.val.1 q.val.2 = g.val := by
      rw [ha]
      exact congrArg Subtype.val hq
    have hxb₂ := q.property.2.1
    have hab₂ : p.val.1 ≠ q.val.2 := ha ▸ q.property.2.2.1
    exact Subtype.ext (MatchingThreeEdgeSwitchIncoming g.val g.property.1.1.1
      x p.val.1 p.val.2 q.val.2 y f₁.val f₂.val
      p.property.1 p.property.2.1 p.property.2.2.1 hxb₂ hab₂
      f₁.property.2.2 f₂.property.2.2 hs₁ hs₂).2
  have switching_count : (∑ f : Min, Fintype.card (Candidates f)) ≤
      n * Fintype.card Mout := by
    let encode (p : Sigma Candidates) : Mout × U :=
      (switchMap p.1 p.2, p.2.val.1)
    have hencode : Function.Injective encode := by
      intro p q hpq
      rcases p with ⟨f₁, p⟩
      rcases q with ⟨f₂, q⟩
      have hg : switchMap f₁ p = switchMap f₂ q := congrArg Prod.fst hpq
      have ha : p.val.1 = q.val.1 := congrArg Prod.snd hpq
      have hf : f₁ = f₂ := incoming_unique (switchMap f₁ p) f₁ f₂ p q rfl hg.symm ha
      subst f₂
      have hpair : p = q := switchMap_injective f₁ hg
      subst q
      rfl
    calc
      (∑ f : Min, Fintype.card (Candidates f)) = Fintype.card (Sigma Candidates) :=
        Fintype.card_sigma.symm
      _ ≤ Fintype.card (Mout × U) := Fintype.card_le_of_injective encode hencode
      _ = n * Fintype.card Mout := by
        rw [Fintype.card_prod, Fintype.card_coe, hU, Nat.mul_comm]
  have candidate_count (f : Min) :
      c * (n : ℝ) ^ 2 ≤ (Fintype.card (Candidates f) : ℝ) + 3 * n :=
    MatchingSwitchCandidateCount G U W hUW n hnpos hU hW ε d hε h4 hd hSR
      k xN yN hxinj hyinj hk f.val f.property.1 f.property.2.1 x y f.property.2.2
  have candidate_lower (f : Min) :
      (c / 2) * (n : ℝ) ^ 2 ≤ (Fintype.card (Candidates f) : ℝ) := by
    have hh := candidate_count f
    linarith
  have switching_lower :
      (c / 2) * (n : ℝ) ^ 2 * Fintype.card Min ≤
        (∑ f : Min, (Fintype.card (Candidates f) : ℝ)) := by
    calc
      _ = ∑ _f : Min, (c / 2) * (n : ℝ) ^ 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun f _ => candidate_lower f)
  have switching_upper :
      (∑ f : Min, (Fintype.card (Candidates f) : ℝ)) ≤
        (n : ℝ) * Fintype.card Mout := by
    exact_mod_cast switching_count
  have matching_ratio :
      (n : ℝ) * (Fintype.card Min : ℝ) ≤
        (2 / c) * (Fintype.card Mout : ℝ) := by
    have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hh := switching_lower.trans switching_upper
    have hh' : (c / 2) * (n : ℝ) * Fintype.card Min ≤ Fintype.card Mout := by
      apply (mul_le_mul_iff_right₀ hnr).mp
      nlinarith [hh]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hh']
  let Match := {f : U → W // PerfectMatching G U W hUW f}
  letI : Nonempty Match := h
  have event_measure (E : Set (U → W)) :
      μ.toOuterMeasure E =
        (Fintype.card {g : Match // g.val ∈ E} : ENNReal) / Fintype.card Match := by
    change ((PMF.uniformOfFintype Match).map Subtype.val).toOuterMeasure E = _
    rw [PMF.toOuterMeasure_map_apply]
    unfold PMF.uniformOfFintype
    rw [PMF.toOuterMeasure_uniformOfFinset_apply]
    simp [Match, Fintype.card_subtype]
  let Cond := {g : Match // g.val ∈ CylinderEvent xN yN}
  have hden : μ.toOuterMeasure (CylinderEvent xN yN) =
      (Fintype.card Cond : ENNReal) / Fintype.card Match := event_measure _
  have hnum : μ.toOuterMeasure
      (CylinderEvent xN yN ∩ CylinderEvent (fun _ : Fin 1 => x) (fun _ => y)) =
      (Fintype.card Min : ENNReal) / Fintype.card Match := by
    rw [event_measure]
    congr 1
    apply congrArg (fun a : ℕ => (a : ENNReal))
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    apply Nat.card_congr
    refine {
      toFun := fun g => ⟨g.val.val, g.val.property, ?_⟩
      invFun := fun g => ⟨⟨g.val, g.property.1⟩, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
    · simpa [CylinderEvent] using g.property
    · simpa [CylinderEvent] using g.property.2
  have houtcond : Fintype.card Mout ≤ Fintype.card Cond := by
    let embed (g : Mout) : Cond := ⟨⟨g.val, g.property.1⟩, g.property.2.1⟩
    apply Fintype.card_le_of_injective embed
    intro a b hab
    exact Subtype.ext (congrArg (fun g : Cond => g.val.val) hab)
  have htotal : (Fintype.card Match : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Match ≠ 0)
  have hcond : (Fintype.card Cond : ENNReal) ≠ 0 := by
    intro hh
    apply hzero
    rw [hden, hh, ENNReal.zero_div]
  have hcondR : (0 : ℝ) < Fintype.card Cond := by
    have hh : Fintype.card Cond ≠ 0 := by exact_mod_cast hcond
    exact_mod_cast Nat.pos_of_ne_zero hh
  have htotalR : (Fintype.card Match : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Match ≠ 0)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hcount : (n : ℝ) * (Fintype.card Min : ℝ) ≤
      max 1 (2 / c) * (Fintype.card Cond : ℝ) := by
    have houtR : (Fintype.card Mout : ℝ) ≤ Fintype.card Cond := by
      exact_mod_cast houtcond
    calc
      _ ≤ (2 / c) * (Fintype.card Mout : ℝ) := matching_ratio
      _ ≤ (2 / c) * (Fintype.card Cond : ℝ) :=
        mul_le_mul_of_nonneg_left houtR (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
  have hreal : (Fintype.card Min : ℝ) / Fintype.card Cond ≤ max 1 (2 / c) / n := by
    apply (div_le_div_iff₀ hcondR hnr).mpr
    simpa only [mul_comm] using hcount
  have hnumtop : μ.toOuterMeasure
      (CylinderEvent xN yN ∩ CylinderEvent (fun _ : Fin 1 => x) (fun _ => y)) ≠ ⊤ := by
    rw [hnum]
    exact ENNReal.div_ne_top (by simp) htotal
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top hnumtop hzero)
    (ENNReal.div_ne_top hCtop (by exact_mod_cast hnpos.ne'))).mp
  simpa only [hnum, hden, ENNReal.toReal_div, ENNReal.toReal_natCast,
    div_div_div_cancel_right₀ htotalR, C,
    ENNReal.toReal_ofReal (le_trans (by norm_num) (le_max_left 1 (2 / c)))] using hreal
