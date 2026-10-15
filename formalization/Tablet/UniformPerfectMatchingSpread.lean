import Tablet.MatchingManyEdges
import Tablet.MatchingSwitching
import Tablet.UniformPerfectMatching
import Tablet.VertexSpreadOn

-- [TABLET NODE: UniformPerfectMatchingSpread]
theorem UniformPerfectMatchingSpread :
    ∀ ε d : ENNReal, 0 < ε → 4 * ε < d → d ≤ 1 →
      ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V]
        [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (U W : Finset V) (hUW : Disjoint U W) (n : ℕ),
        n₀ ≤ n → U.card = n → W.card = n → SuperRegularPair G U W ε d →
        ∀ h : Nonempty {f : U → W // PerfectMatching G U W hUW f},
          VertexSpreadOn ((UniformPerfectMatching G U W hUW h).map Subtype.val)
            (C / n) Set.univ := by
-- BODY
  classical
  intro ε d hε h4 hd
  have h2 : 2 * ε < d := lt_of_le_of_lt
    (mul_le_mul_right' (by norm_num : (2 : ENNReal) ≤ 4) ε) h4
  obtain ⟨Cm, hCm, hCmtop, nm, hm⟩ := MatchingManyEdges ε d hε h2 hd
  obtain ⟨Cs, hCs, hCstop, ns, hs⟩ := MatchingSwitching ε d hε h4 hd
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd
  have hdpos : 0 < d := lt_of_le_of_lt bot_le h4
  have hdR : 0 < d.toReal := ENNReal.toReal_pos hdpos.ne' hdtop
  obtain ⟨r, hr⟩ := exists_nat_gt (2 / d.toReal)
  have hr2 : 2 ≤ d.toReal * (r : ℝ) := by
    have ht := (div_lt_iff₀ hdR).mp hr
    nlinarith
  let C : ENNReal := max Cs (Cm ^ r)
  have hC : 1 ≤ C := hCs.trans (le_max_left _ _)
  have hCtop : C ≠ ⊤ := by
    simp only [C, ne_eq, max_eq_top]
    exact not_or.mpr ⟨hCstop, ENNReal.pow_ne_top hCmtop⟩
  obtain ⟨m, hmC⟩ := exists_nat_gt C.toReal
  refine ⟨C, hC, hCtop, max (max nm ns) (m + 1), ?_⟩
  intro V _ _ G _ U W hUW n hn hU hW hreg h
  have hnm : nm ≤ n := (le_max_left nm ns).trans ((le_max_left _ _).trans hn)
  have hns : ns ≤ n := (le_max_right nm ns).trans ((le_max_left _ _).trans hn)
  have hmn : m + 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hnzero : (n : ENNReal) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hCn : C ≤ n := by
    apply (ENNReal.toReal_le_toReal hCtop (ENNReal.natCast_ne_top n)).mp
    have hh : (m : ℝ) < n := by exact_mod_cast (show m < n by omega)
    simpa using (hmC.trans hh).le
  let μ := (UniformPerfectMatching G U W hUW h).map Subtype.val
  change VertexSpreadOn μ (C / n) Set.univ
  refine ⟨(ENNReal.div_le_iff hnzero (ENNReal.natCast_ne_top n)).mpr
    (by simpa using hCn), ?_⟩
  intro s x y hx _
  by_cases hzero : μ.toOuterMeasure (CylinderEvent x y) = 0
  · rw [hzero]
    exact bot_le
  -- A positive cylinder has a matching in the support, certifying all its edges.
  have hnot : ¬ Disjoint μ.support (CylinderEvent x y) := by
    exact fun hh => hzero ((μ.toOuterMeasure_apply_eq_zero_iff _).mpr hh)
  obtain ⟨f, hf, hfe⟩ := Set.not_disjoint_iff.mp hnot
  obtain ⟨g, _, hgf⟩ := (PMF.mem_support_map_iff _ _ _).mp hf
  have hmatch : PerfectMatching G U W hUW f := hgf ▸ g.property
  have hy : Function.Injective y := by
    intro i j hij
    apply hx
    apply hmatch.1.1
    rw [hfe i, hfe j, hij]
  have hedge : ∀ i, G.Adj (x i) (y i) := by
    intro i
    rw [← hfe i]
    exact hmatch.2 (x i)
  by_cases hlarge : d * n / 2 ≤ (s : ENNReal)
  · have hlargeR : d.toReal * (n : ℝ) / 2 ≤ (s : ℝ) := by
      have hh := (ENNReal.toReal_le_toReal
        (ENNReal.div_ne_top (ENNReal.mul_ne_top hdtop (by simp)) (by norm_num))
        (ENNReal.natCast_ne_top s)).mpr hlarge
      simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat] using hh
    have hnrs : n ≤ r * s := by
      have hh : (n : ℝ) ≤ (r : ℝ) * s := by
        have ht := mul_le_mul_of_nonneg_left hlargeR (Nat.cast_nonneg r)
        have hu := mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg n)
        nlinarith
      exact_mod_cast hh
    calc
      μ.toOuterMeasure (CylinderEvent x y) ≤ Cm ^ n / (n : ENNReal) ^ s :=
        hm G U W hUW n hnm hU hW hreg h s x y hx
      _ ≤ C ^ s / (n : ENNReal) ^ s := by
        apply ENNReal.div_le_div_right
        calc
          Cm ^ n ≤ Cm ^ (r * s) := pow_le_pow_right₀ hCm hnrs
          _ = (Cm ^ r) ^ s := pow_mul _ _ _
          _ ≤ C ^ s := pow_le_pow_left' (le_max_right _ _) s
      _ = (C / n) ^ s := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  · have hsmall : (s : ENNReal) < d * n / 2 := lt_of_not_ge hlarge
    let idx (k : ℕ) (hk : k ≤ s) (i : Fin k) : Fin s :=
      ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
    let E (k : ℕ) (hk : k ≤ s) := CylinderEvent (x ∘ idx k hk) (y ∘ idx k hk)
    have hmass (A : Set (U → W)) : μ.toOuterMeasure A ≤ 1 := by
      apply (μ.toOuterMeasure.mono (Set.subset_univ A)).trans_eq
      exact (μ.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)
    have hprefix : ∀ k (hk : k ≤ s), μ.toOuterMeasure (E k hk) ≤ (C / n) ^ k := by
      intro k
      induction k with
      | zero =>
          intro hk
          simpa only [pow_zero] using hmass (E 0 hk)
      | succ k ih =>
          intro hks
          have hk : k ≤ s := by omega
          let z : Fin s := ⟨k, by omega⟩
          have hsplit : E (k + 1) hks =
              E k hk ∩ CylinderEvent (fun _ : Fin 1 => x z) (fun _ => y z) := by
            ext a
            constructor
            · intro ha
              refine ⟨?_, ?_⟩
              · intro i
                exact ha ⟨i.val, by omega⟩
              · intro i
                exact ha ⟨k, Nat.lt_succ_self k⟩
            · rintro ⟨ha, hb⟩ i
              by_cases hi : i.val < k
              · exact ha ⟨i.val, hi⟩
              · have hi' : i.val = k := by omega
                have hiZ : idx (k + 1) hks i = z := Fin.ext hi'
                simpa only [E, CylinderEvent, Set.mem_setOf_eq, Function.comp_apply, hiZ]
                  using hb (0 : Fin 1)
          by_cases hz : μ.toOuterMeasure (E k hk) = 0
          · have hnext : μ.toOuterMeasure (E (k + 1) hks) = 0 := by
              apply le_antisymm _ bot_le
              rw [hsplit]
              exact (μ.toOuterMeasure.mono Set.inter_subset_left).trans_eq hz
            rw [hnext]
            exact bot_le
          · have hidx : Function.Injective (idx k hk) := by
              intro a b hab
              exact Fin.ext (congrArg (fun i : Fin s => i.val) hab)
            have hxnew : x z ∉ Set.range (x ∘ idx k hk) := by
              rintro ⟨i, hi⟩
              have hh := congrArg Fin.val (hx hi)
              change i.val = k at hh
              omega
            have hynew : y z ∉ Set.range (y ∘ idx k hk) := by
              rintro ⟨i, hi⟩
              have hh := congrArg Fin.val (hy hi)
              change i.val = k at hh
              omega
            have hkbound : (k : ENNReal) ≤ d * n / 2 :=
              (by exact_mod_cast hk : (k : ENNReal) ≤ s).trans hsmall.le
            have hstep := hs G U W hUW n hns hU hW hreg h k
              (x ∘ idx k hk) (y ∘ idx k hk) (hx.comp hidx) (hy.comp hidx)
              (fun i => hedge (idx k hk i)) hkbound (x z) (y z) hxnew hynew (hedge z)
            change μ.toOuterMeasure
              (E k hk ∩ CylinderEvent (fun _ : Fin 1 => x z) (fun _ => y z)) /
              μ.toOuterMeasure (E k hk) ≤ Cs / n at hstep
            rw [← hsplit] at hstep
            have hfinite : μ.toOuterMeasure (E k hk) ≠ ⊤ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top (hmass _)
            calc
              μ.toOuterMeasure (E (k + 1) hks) =
                  (μ.toOuterMeasure (E (k + 1) hks) / μ.toOuterMeasure (E k hk)) *
                    μ.toOuterMeasure (E k hk) := (ENNReal.div_mul_cancel hz hfinite).symm
              _ ≤ (C / n) * (C / n) ^ k := mul_le_mul'
                (hstep.trans (ENNReal.div_le_div_right (le_max_left _ _) _)) (ih hk)
              _ = (C / n) ^ (k + 1) := (pow_succ' _ _).symm
    have hfull : E s le_rfl = CylinderEvent x y := by
      ext a
      rfl
    simpa only [hfull] using hprefix s le_rfl
