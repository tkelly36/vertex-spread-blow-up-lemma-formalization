import Tablet.BlowUpInstance
import Tablet.CandidacySystem
import Tablet.CandidacyLowerSuperRegular
import Tablet.InstanceLowerSuperRegular
import Tablet.UniformSubsetIntersectionLaw
import Tablet.HypergeometricTwoTail
import Tablet.ProductPermutationIntersectionTail

open scoped Classical

-- [TABLET NODE: PrescribedHostPartitionSample]
theorem PrescribedHostPartitionSample {r k : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel G.Adj] (B : BlowUpInstance r VH VG H G R)
    (A : CandidacySystem B) (σ : VH → Fin r × Fin k)
    (ε d : ENNReal) (n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hε : 0 < ε) (hε1 : ε < 1) (hd : d ≤ 1)
    (hproj : ∀ x, (σ x).1 = B.sourceCluster x)
    (hcard : ∀ i,
      (Finset.univ.filter fun x => B.sourceCluster x = i).card = n ∧
      (Finset.univ.filter fun v => B.hostCluster v = i).card = n)
    (hsize : ∀ p, (Finset.univ.filter fun x => σ x = p).card = n / k ∨
      (Finset.univ.filter fun x => σ x = p).card = n / k + 1)
    (hhost : InstanceLowerSuperRegular B ε d)
    (hcand : CandidacyLowerSuperRegular B A ε d)
    (htail : 2 * (r : ℝ) * k * (r + 1) * n *
      Real.exp (-((ε.toReal / (2 * k)) ^ 2 /
        (2 * (1 + ε.toReal / (6 * k)))) * n) < 1) :
    ∃ f : VG → Fin r × Fin k,
      (∀ v, (f v).1 = B.hostCluster v) ∧
      (∀ p, (Finset.univ.filter fun v => f v = p).card =
        (Finset.univ.filter fun x => σ x = p).card) ∧
      (∀ x j, (d - 2 * ε) *
        ((Finset.univ.filter fun v => f v = (B.sourceCluster x, j)).card : ENNReal) ≤
        ((Finset.univ.filter fun v =>
          f v = (B.sourceCluster x, j) ∧ A.allowed x v).card : ENNReal)) ∧
      (∀ v i j, R.Adj (B.hostCluster v) i →
        (d - 2 * ε) * ((Finset.univ.filter fun w => f w = (i, j)).card : ENNReal) ≤
        ((Finset.univ.filter fun w => f w = (i, j) ∧ G.Adj v w).card : ENNReal)) := by
-- BODY
  classical
  let F (i : Fin r) := {v : VG // B.hostCluster v = i}
  let X (i : Fin r) := {x : VH // B.sourceCluster x = i}
  have hF (i : Fin r) : Fintype.card (F i) = n := by
    simpa only [F, Fintype.card_subtype] using (hcard i).2
  have hX (i : Fin r) : Fintype.card (X i) = n := by
    simpa only [X, Fintype.card_subtype] using (hcard i).1
  let e (i : Fin r) : F i ≃ X i := Fintype.equivOfCardEq ((hF i).trans (hX i).symm)
  let S (p : Fin r × Fin k) : Finset (F p.1) :=
    Finset.univ.filter fun v => σ (e p.1 v).val = p
  have hS (p : Fin r × Fin k) : (S p).card =
      (Finset.univ.filter fun x => σ x = p).card := by
    apply Finset.card_bij (fun v _ => (e p.1 v).val)
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact (e p.1).injective (Subtype.ext h)
    · intro x hx
      have hxσ := (Finset.mem_filter.mp hx).2
      have hxB : B.sourceCluster x = p.1 := by rw [← hproj x, hxσ]
      refine ⟨(e p.1).symm ⟨x, hxB⟩, ?_, ?_⟩
      · simp [S, hxσ]
      · simp
  have hsum (i : Fin r) : ∑ j : Fin k, (S (i, j)).card = n := by
    have hsplit (j : Fin k) :
        ((Finset.univ.filter fun x => B.sourceCluster x = i).filter
          fun x => (σ x).2 = j) = (Finset.univ.filter fun x => σ x = (i, j)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff, hproj]
    simp_rw [hS, ← hsplit]
    simpa only [Finset.mem_univ, Finset.filter_true, (hcard i).1] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter fun x => B.sourceCluster x = i) Finset.univ
        (fun x => (σ x).2)
  let Ω := ∀ i, Equiv.Perm (F i)
  let f (ω : Ω) (v : VG) : Fin r × Fin k :=
    σ (e (B.hostCluster v) ((ω (B.hostCluster v)).symm ⟨v, rfl⟩)).val
  have hfon (ω : Ω) (i : Fin r) (v : F i) :
      f ω v.val = σ (e i ((ω i).symm v)).val := by
    rcases v with ⟨v, hv⟩
    subst i
    rfl
  have hf (ω : Ω) (v : VG) : (f ω v).1 = B.hostCluster v := by
    dsimp [f]
    rw [hproj]
    exact (e _ _).property
  have hmem (ω : Ω) (p : Fin r × Fin k) (v : F p.1) :
      f ω v.val = p ↔ v ∈ (S p).image (ω p.1) := by
    rw [hfon]
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨(ω p.1).symm v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, (ω p.1).apply_symm_apply v⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
      rw [← heq, (ω p.1).symm_apply_apply]
      exact (Finset.mem_filter.mp hw).2
  have hcount (ω : Ω) (p : Fin r × Fin k) (Q : VG → Prop) [DecidablePred Q] :
      (Finset.univ.filter fun v => f ω v = p ∧ Q v).card =
        (((S p).image (ω p.1)).filter fun v => Q v.val).card := by
    symm
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      obtain ⟨hv, hQ⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(hmem ω p v).mpr hv, hQ⟩⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro v hv
      obtain ⟨hlabel, hQ⟩ := (Finset.mem_filter.mp hv).2
      have hvB : B.hostCluster v = p.1 := (hf ω v).symm.trans (congrArg Prod.fst hlabel)
      exact ⟨⟨v, hvB⟩, Finset.mem_filter.mpr ⟨(hmem ω p ⟨v, hvB⟩).mp hlabel, hQ⟩, rfl⟩
  have hcapacity (ω : Ω) (p : Fin r × Fin k) :
      (Finset.univ.filter fun v => f ω v = p).card = (S p).card := by
    simpa only [and_true, Finset.filter_true,
      Finset.card_image_of_injective _ (ω p.1).injective] using hcount ω p (fun _ => True)
  by_cases htrivial : d ≤ 2 * ε
  · refine ⟨f (fun _ => Equiv.refl _), hf (fun _ => Equiv.refl _), ?_, ?_, ?_⟩
    · intro p
      exact (hcapacity (fun _ => Equiv.refl _) p).trans (hS p)
    · intro x j
      simp [tsub_eq_zero_of_le htrivial]
    · intro v i j _
      simp [tsub_eq_zero_of_le htrivial]
  have hkpos : 0 < k := by omega
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hεfinite : ε ≠ ⊤ := ne_top_of_lt hε1
  have hdfinite : d ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd
  have heR : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεfinite
  have htwo : 2 * ε < d := lt_of_not_ge htrivial
  have heled : ε ≤ d := by
    exact (show ε ≤ 2 * ε by
      simpa using mul_le_mul_left (show (1 : ENNReal) ≤ 2 by norm_num) ε).trans htwo.le
  let a : ℝ := ε.toReal / (2 * k)
  let q : ℝ := 2 * Real.exp (-(a ^ 2 / (2 * (1 + a / 3))) * n)
  have ha : 0 < a := div_pos heR (by positivity)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmin (p : Fin r × Fin k) : (n : ℝ) / (2 * k) ≤ (S p).card := by
    have hmpos : 1 ≤ n / k := Nat.div_pos (by omega) hkpos
    have hmR : (1 : ℝ) ≤ (n / k : ℕ) := by exact_mod_cast hmpos
    have hfloor : (n : ℝ) < (k : ℝ) * ((n / k : ℕ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ n hkpos
    have hnk : (n : ℝ) ≤ 2 * (k : ℝ) * (n / k : ℕ) := by nlinarith only [hfloor, hmR, hkR]
    have hs : n / k ≤ (S p).card := by
      rw [hS]
      rcases hsize p with h | h <;> omega
    apply (div_le_iff₀ (by positivity : 0 < 2 * (k : ℝ))).mpr
    have hsR : (n / k : ℕ) ≤ ((S p).card : ℝ) := by exact_mod_cast hs
    nlinarith only [hnk, hsR, hkR]
  have hsubcount (i : Fin r) (Q : VG → Prop) [DecidablePred Q] :
      ((Finset.univ : Finset (F i)).filter fun v => Q v.val).card =
        ((Finset.univ.filter fun v => B.hostCluster v = i).filter Q).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.property⟩,
        (Finset.mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro v hv
      obtain ⟨hv, hQ⟩ := Finset.mem_filter.mp hv
      exact ⟨⟨v, (Finset.mem_filter.mp hv).2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩, rfl⟩
  let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
    ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ q = Sum.inr v ∧ A.allowed x v
  letI : DecidableRel C.Adj := Classical.decRel _
  let left (T : Finset VH) : Finset (VH ⊕ VG) := T.map Function.Embedding.inl
  let right (T : Finset VG) : Finset (VH ⊕ VG) := T.map Function.Embedding.inr
  have hadj (x : VH) (v : VG) : C.Adj (Sum.inl x) (Sum.inr v) ↔ A.allowed x v := by
    simp [C, SimpleGraph.fromRel_adj]
  have hpair (i : Fin r) : LowerSuperRegularPair C
      (left (Finset.univ.filter fun x => B.sourceCluster x = i))
      (right (Finset.univ.filter fun v => B.hostCluster v = i)) ε d := by
    have hl : left (Finset.univ.filter fun x => B.sourceCluster x = i) =
        Finset.univ.filter (fun z : VH ⊕ VG =>
          ∃ x : VH, z = Sum.inl x ∧ B.sourceCluster x = i) := by
      ext z
      cases z <;> simp [left]
    have hr : right (Finset.univ.filter fun v => B.hostCluster v = i) =
        Finset.univ.filter (fun z : VH ⊕ VG =>
          ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = i) := by
      ext z
      cases z <;> simp [right]
    rw [hl, hr]
    exact hcand i
  have hcandDegree (x : VH) : (d - ε) * n ≤
      (((Finset.univ : Finset (F (B.sourceCluster x))).filter
        fun v => A.allowed x v.val).card : ENNReal) := by
    have h := (hpair (B.sourceCluster x)).2.1 (Sum.inl x) (by simp [left])
    rw [hsubcount (B.sourceCluster x) (fun v => A.allowed x v)]
    simpa only [right, Finset.filter_map, Finset.card_map, Function.comp_def,
      Function.Embedding.inr_apply, hadj, (hcard (B.sourceCluster x)).2] using h
  have hhostDegree (v : VG) (i : Fin r) (hvi : R.Adj (B.hostCluster v) i) :
      (d - ε) * n ≤ (((Finset.univ : Finset (F i)).filter
        fun w => G.Adj v w.val).card : ENNReal) := by
    rw [hsubcount i (fun w => G.Adj v w)]
    have h := (hhost hvi).2.1 v (by simp)
    simpa only [(hcard i).2] using h
  -- Positive degree failures lie in the strict hypergeometric deviation event.
  have hfailure (p : Fin r × Fin k) (t z : ℕ)
      (ht : (d - ε) * n ≤ (t : ENNReal))
      (hz : (z : ENNReal) < (d - 2 * ε) * (S p).card) :
      a * n < |(z : ℝ) - ((S p).card : ℝ) * t / n| := by
    have htR : (d.toReal - ε.toReal) * n ≤ (t : ℝ) := by
      have hh := (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mpr ht
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le heled hdfinite,
        ENNReal.toReal_natCast] using hh
    have hzR : (z : ℝ) < (d.toReal - 2 * ε.toReal) * (S p).card := by
      have hh := (ENNReal.toReal_lt_toReal (by simp) (by finiteness)).mpr hz
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le htwo.le hdfinite,
        ENNReal.toReal_natCast, ENNReal.toReal_ofNat] using hh
    have hmean : (d.toReal - ε.toReal) * (S p).card ≤ ((S p).card : ℝ) * t / n := by
      apply (le_div_iff₀ hnR).mpr
      have hh := mul_le_mul_of_nonneg_left htR (Nat.cast_nonneg (S p).card : (0 : ℝ) ≤ _)
      nlinarith only [hh]
    have hslack : a * n ≤ ε.toReal * (S p).card := by
      have hh := mul_le_mul_of_nonneg_left (hmin p) heR.le
      convert hh using 1
      dsimp [a]
      ring
    apply lt_of_le_of_lt hslack
    apply lt_of_lt_of_le _ (neg_le_abs _)
    linarith only [hzR, hmean]
  let bad (p : Fin r × Fin k) (Q : VG → Prop) [DecidablePred Q] : Finset Ω :=
    Finset.univ.filter fun ω =>
      ((((S p).image (ω p.1)).filter fun v => Q v.val).card : ENNReal) <
        (d - 2 * ε) * (S p).card
  have hbad (p : Fin r × Fin k) (Q : VG → Prop) [DecidablePred Q]
      (hdegree : (d - ε) * n ≤
        (((Finset.univ : Finset (F p.1)).filter fun v => Q v.val).card : ENNReal)) :
      ((bad p Q).card : ℝ) / (Fintype.card Ω : ℝ) ≤ q := by
    let T : Finset (F p.1) := Finset.univ.filter fun v => Q v.val
    have heq (U : Finset (F p.1)) : (U.filter fun v => Q v.val) = U ∩ T := by
      ext v
      simp [T]
    have hcontain : bad p Q ⊆ Finset.univ.filter (fun (ω : Ω) =>
        a * n < |(((S p).image (ω p.1) ∩ T).card : ℝ) - (S p).card * T.card / n|) := by
      intro ω hω
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hfailure p T.card _ hdegree ?_⟩
      simpa only [← heq] using (Finset.mem_filter.mp hω).2
    exact (div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hcontain)
      (Nat.cast_nonneg _)).trans (ProductPermutationIntersectionTail F p.1 (S p) T n
        (hF p.1) hnpos a ha)
  have hVH : Fintype.card VH = r * n := by
    calc
      _ = Fintype.card (Σ i, X i) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv B.sourceCluster).symm
      _ = ∑ i : Fin r, Fintype.card (X i) := Fintype.card_sigma
      _ = r * n := by simp only [hX, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  have hVG : Fintype.card VG = r * n := by
    calc
      _ = Fintype.card (Σ i, F i) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv B.hostCluster).symm
      _ = ∑ i : Fin r, Fintype.card (F i) := Fintype.card_sigma
      _ = r * n := by simp only [hF, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
  let J := (VH × Fin k) ⊕ (VG × (Fin r × Fin k))
  let D : J → Finset Ω := fun t => match t with
    | Sum.inl (x, j) => bad (B.sourceCluster x, j) (fun v => A.allowed x v)
    | Sum.inr (v, i, j) => if R.Adj (B.hostCluster v) i then
        bad (i, j) (fun w => G.Adj v w) else ∅
  have hD (t : J) : ((D t).card : ℝ) / (Fintype.card Ω : ℝ) ≤ q := by
    rcases t with ⟨x, j⟩ | ⟨v, i, j⟩
    · exact hbad (B.sourceCluster x, j) (fun v => A.allowed x v) (hcandDegree x)
    · by_cases hvi : R.Adj (B.hostCluster v) i
      · simpa only [D, if_pos hvi] using
          hbad (i, j) (fun w => G.Adj v w) (hhostDegree v i hvi)
      · simpa only [D, if_neg hvi, Finset.card_empty, Nat.cast_zero, zero_div] using hq
  have hJ : Fintype.card J = r * n * k + r * n * (r * k) := by
    simp only [J, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hVH, hVG]
  have hsmall : (Fintype.card J : ℝ) * q < 1 := by
    have hden : a / 3 = ε.toReal / (6 * k) := by dsimp [a]; ring
    have heq : (Fintype.card J : ℝ) * q =
        2 * (r : ℝ) * k * (r + 1) * n *
          Real.exp (-((ε.toReal / (2 * k)) ^ 2 /
            (2 * (1 + ε.toReal / (6 * k)))) * n) := by
      rw [hJ]
      simp only [Nat.cast_add, Nat.cast_mul]
      dsimp [q]
      rw [hden]
      dsimp [a]
      ring
    rwa [heq]
  let E : Finset Ω := Finset.univ.biUnion D
  have hΩ : 0 < Fintype.card Ω :=
    Fintype.card_pos_iff.mpr ⟨fun _ => Equiv.refl _⟩
  have hΩR : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hEprob : (E.card : ℝ) / (Fintype.card Ω : ℝ) < 1 := by
    calc
      _ ≤ (∑ t : J, ((D t).card : ℝ)) / (Fintype.card Ω : ℝ) := by
        apply div_le_div_of_nonneg_right _ hΩR.le
        exact_mod_cast (Finset.card_biUnion_le : E.card ≤ ∑ t : J, (D t).card)
      _ = ∑ t : J, ((D t).card : ℝ) / (Fintype.card Ω : ℝ) := Finset.sum_div ..
      _ ≤ ∑ _t : J, q := Finset.sum_le_sum fun t _ => hD t
      _ = (Fintype.card J : ℝ) * q := by simp
      _ < 1 := hsmall
  have hEcard : E.card < (Finset.univ : Finset Ω).card := by
    have h := (div_lt_iff₀ hΩR).mp hEprob
    simp only [one_mul] at h
    simpa only [Finset.card_univ] using (show E.card < Fintype.card Ω by exact_mod_cast h)
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hEcard
  have hgood (t : J) : ω ∉ D t := by
    intro ht
    exact hω (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ht⟩)
  refine ⟨f ω, hf ω, ?_, ?_, ?_⟩
  · intro p
    exact (hcapacity ω p).trans (hS p)
  · intro x j
    rw [hcapacity ω (B.sourceCluster x, j),
      hcount ω (B.sourceCluster x, j) (fun v => A.allowed x v)]
    apply le_of_not_gt
    intro hbadω
    exact hgood (Sum.inl (x, j)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadω⟩)
  · intro v i j hvi
    rw [hcapacity ω (i, j), hcount ω (i, j) (fun w => G.Adj v w)]
    apply le_of_not_gt
    intro hbadω
    have hh := hgood (Sum.inr (v, i, j))
    simp only [D, if_pos hvi] at hh
    exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadω⟩)
