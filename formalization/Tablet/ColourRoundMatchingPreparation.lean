import Tablet.ColourRoundStepParameters
import Tablet.ColourRoundUntouchedGeometry
import Tablet.ColourRoundInvariant
import Tablet.InstanceSuperRegular
import Tablet.SaturatingSourcePair
import Tablet.EqualSizeSourceWitnessTransport
import Tablet.CurrentExtraSourceWitnessTransport
import Tablet.FutureExtraSourceWitnessTransport
import Tablet.NearEqualVaryingGoodEdgeSuperRegularity
import Tablet.OneClusterExtension
import Tablet.VertexSpreadMonotone
import Tablet.ColourRoundRetainedTriplets
import Tablet.ColourRoundMatchingRecords
import Tablet.FiniteTripletRelabelling

-- [TABLET NODE: ColourRoundMatchingPreparation]
theorem ColourRoundMatchingPreparation
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel G.Adj] [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q)
    (theta density epsilon rho eta omega xi : ℕ → ENNReal)
    (D : ℕ) (d C a : ENNReal) (n round : ℕ)
    (P : ColourRoundStepParameters D q d C a n round
      theta density epsilon rho eta omega xi)
    (hsizes : ∀ j : Fin r,
      ((Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n ∨
       (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n + 1) ∧
      (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card =
        (Finset.univ.filter fun v : VG => B.hostCluster v = j).card)
    (hhost : InstanceSuperRegular B (epsilon 0) d)
    (hsource : ∀ ⦃i j : Fin r⦄, R.Adj i j → SaturatingSourcePair B i j)
    (touched : Finset (Fin r)) (X : Finset VH)
    (mu : PMF (PartialCompatibleEmbedding B A X))
    (hinv : ColourRoundInvariant B A colour epsilon density D C n round touched X mu)
    (i : Fin r) (hi : (colour i).val = round) (hiS : i ∉ touched)
    (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) :
    let X' := Finset.univ.filter fun x : VH =>
      (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ insert i touched
    let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
    ∃ (nu0 : PMF (PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y))
      (E : Set (PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y))
      (hE : ∃ g ∈ E, g ∈ nu0.support),
      (2 : ENNReal)⁻¹ ≤ nu0.toOuterMeasure E ∧
      VertexSpreadOn (nu0.map fun g => fun y : Y => g.toFun y.1)
        (C / (2 * n)) Set.univ ∧
      VertexSpreadOn ((nu0.filter E hE).map fun g => fun y : Y => g.toFun y.1)
        (C / n) Set.univ ∧
      (∀ g ∈ (nu0.filter E hE).support,
        ∀ h : PartialCompatibleEmbedding B A X',
        (∀ x ∈ X, h.toFun x = f.toFun x) →
        (∀ y ∈ Y, h.toFun y = g.toFun y) →
        ∀ j : Fin r, R.Adj i j → j ∉ touched → round ≤ (colour j).val →
          let exposure := (Finset.univ.filter fun k : Fin r =>
            ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
          let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
            ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X'
          let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
            ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧ v ∉ X'.image h.toFun
          let Aj : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
            ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
              (y, v) ∈ UpdatedCandidacyCluster B A X' h j
          ∃ W : SimpleGraph (VH ⊕ VG), W ≤ Aj ∧
            @SuperRegularPair (VH ⊕ VG) _ W (Classical.decRel _)
              L Q (epsilon (round + 1)) (density (exposure + 1))) := by
-- BODY
  classical
  let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
  let K0 := Finset.univ.filter fun v : VG => B.hostCluster v = i
  let U := Y.image (Sum.inl : VH → VH ⊕ VG)
  let K := K0.image (Sum.inr : VG → VH ⊕ VG)
  let J := {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val}
  let Z : J → Finset (VH ⊕ VG) := fun j =>
    (Finset.univ.filter fun v : VG => B.hostCluster v = j).image Sum.inr
  let exposure := fun j : Fin r => (Finset.univ.filter fun k : Fin r =>
    ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
  let m := Y.card
  have heta : eta round < 1 := by
    have h : eta round ≤ 2 * eta round := by
      simpa only [one_mul] using mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2) (eta round)
    exact h.trans_lt (P.host_density_upper.trans_le tsub_le_self)
  have hn : 1 ≤ n := by
    by_contra h
    have hz : n = 0 := by omega
    have hfin := P.integer_reserve.trans_lt (P.inner_reserve.trans heta)
    simp [hz] at hfin
  have hnm : n ≤ m := by
    rcases (hsizes i).1 with h | h <;> change n ≤ Y.card <;> change Y.card = _ at h <;> omega
  have hm : 0 < m := lt_of_lt_of_le (by omega) hnm
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmt : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hU : U.card = m := by simp [U, m, Finset.card_image_of_injective, Sum.inl_injective]
  have hK : K.card = m := by
    simp only [K, Finset.card_image_of_injective _ Sum.inr_injective]
    exact (hsizes i).2.symm
  have hUK : Disjoint U K := by
    apply Finset.disjoint_left.mpr
    intro z hz hk
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, _, h⟩ := Finset.mem_image.mp hk
    cases h
  obtain ⟨F, F13, F23, hFA, hF, htrip, htransport⟩ :=
    ColourRoundRetainedTriplets B A colour theta density epsilon rho eta omega xi
      D d C a n round P hn hsizes hhost hsource touched X mu hinv i hi hiS f hf
  letI : DecidableRel F.Adj := Classical.decRel _
  letI : ∀ j, DecidableRel (F13 j).Adj := fun _ => Classical.decRel _
  letI : ∀ j, DecidableRel (F23 j).Adj := fun _ => Classical.decRel _
  have geom := ColourRoundUntouchedGeometry R colour D round touched i
    hinv.2.1 hinv.2.2.1 hinv.2.2.2.1 hi hiS
  have hx : exposure i ≤ D := by
    apply (Finset.card_le_card ?_).trans (hinv.2.1 i)
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.2⟩
  have hy (j : J) : exposure j < D := (geom.2.2.2 j j.property.1).1
  have hJ : Fintype.card J ≤ D := by
    change Fintype.card {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val} ≤ D
    rw [Fintype.card_subtype]
    apply (Finset.card_le_card ?_).trans (hinv.2.1 i)
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  have hrho : rho (exposure i) ≤ 1 := by
    have h := (P.witness_density (exposure i) hx).2
    have hpos : 0 < 1 - rho (exposure i) := lt_of_le_of_lt bot_le h
    exact (lt_of_not_ge fun hh => by simpa [tsub_eq_zero_of_le hh] using hpos).le
  let eEx := (Fintype.equivFin (VH ⊕ VG)).trans (Equiv.ulift.symm)
  obtain ⟨eUEx, eKEx, hUKEx, eMEx, heUEx, heKEx, heMEx, hregEx, _, _⟩ :=
    FiniteTripletRelabelling eEx F U K hUK
  have hMEx := P.certificate.matchingExistenceGuarantee round P.round_bound (exposure i) hx
      (F.comap eEx.symm) (U.image eEx) (K.image eEx) hUKEx m
      ((P.scalar_thresholds _ hx).2.2.2.1.trans hnm)
      (by simpa only [Finset.card_image_of_injective _ eEx.injective] using hU)
      (by simpa only [Finset.card_image_of_injective _ eEx.injective] using hK)
      ((hregEx _ _).mp hF)
  have hM : Nonempty {sigma : U → K // PerfectMatching F U K hUK sigma} :=
    hMEx.map eMEx.symm
  let M := {sigma : U → K // PerfectMatching F U K hUK sigma}
  let mu0 : PMF M := UniformPerfectMatching F U K hUK hM
  let muf : PMF (U → K) := mu0.map Subtype.val
  obtain ⟨e, v, lift, he, hv, hlift, hcontain⟩ :=
    ColourRoundMatchingRecords B A colour round touched X f i hi hiS
      hinv.2.2.2.2.1 (Finset.card_pos.mp hm) F hUK hFA hM
  let Cm : ENNReal := C * m / n
  have halve (T : ENNReal) (s : ℕ) : T / (2 * s) = (T / s) / 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    ac_rfl
  have hCm : Cm / m = C / n := by
    dsimp only [Cm]
    simp only [div_eq_mul_inv]
    calc
      C * m * (n : ENNReal)⁻¹ * (m : ENNReal)⁻¹ =
          C * (n : ENNReal)⁻¹ * ((m : ENNReal) * (m : ENNReal)⁻¹) := by ac_rfl
      _ = C * (n : ENNReal)⁻¹ := by rw [ENNReal.mul_inv_cancel hm0 hmt, mul_one]
  have hCm2 : Cm / (2 * m) = C / (2 * n) := by rw [halve, hCm, ← halve]
  have hhalfunit : C / (2 * n) ≤ 1 := by
    rw [halve]
    have h : (C / n) / 2 ≤ C / n := by
      simpa only [div_eq_mul_inv, mul_one] using
        mul_le_mul_left' (by norm_num : (2 : ENNReal)⁻¹ ≤ 1) (C / n)
    exact h.trans P.spread_unit
  let eSp := (Fintype.equivFin (VH ⊕ VG)).trans (Equiv.ulift.symm)
  obtain ⟨eUSp, eKSp, hUKSp, eMSp, heUSp, heKSp, heMSp, hregSp, _, _⟩ :=
    FiniteTripletRelabelling eSp F U K hUK
  let hMSp := hM.map eMSp
  let muSp := UniformPerfectMatching (F.comap eSp.symm) (U.image eSp) (K.image eSp) hUKSp hMSp
  have hrawSp := P.certificate.matchingGuarantee round P.round_bound (exposure i) hx
    (F.comap eSp.symm) (U.image eSp) (K.image eSp) hUKSp m
    ((P.scalar_thresholds _ hx).2.2.1.trans hnm)
    (by simpa only [Finset.card_image_of_injective _ eSp.injective] using hU)
    (by simpa only [Finset.card_image_of_injective _ eSp.injective] using hK)
    ((hregSp _ _).mp hF) hMSp
  have uniformSp : mu0.map eMSp = muSp := by
    letI := hM
    letI := hMSp
    ext s
    rw [PMF.map_apply, ← eMSp.symm.tsum_eq]
    simp only [eMSp.apply_symm_apply, mu0, muSp, UniformPerfectMatching,
      PMF.uniformOfFintype_apply, Fintype.card_eq_nat_card, Nat.card_congr eMSp]
    simp
  have hrawAmb : VertexSpreadOn (mu0.map fun sigma u => (sigma.val u : VH ⊕ VG))
      (P.certificate.matchingConstant round (exposure i) / m) Set.univ := by
    refine ⟨hrawSp.1, ?_⟩
    intro s x y hxi _
    have hh := hrawSp.2 s (fun k => eUSp (x k)) (fun k => eSp (y k))
      (eUSp.injective.comp hxi) (fun _ => Set.mem_univ _)
    change VertexSpreadOn _ _ _ at hrawSp
    change (muSp.map _).toOuterMeasure _ ≤ _ at hh
    rw [← uniformSp, PMF.map_comp, PMF.toOuterMeasure_map_apply] at hh
    rw [PMF.toOuterMeasure_map_apply]
    have eqset : (fun sigma : M => fun u => ((eMSp sigma).val u).val) ⁻¹'
        CylinderEvent (fun k => eUSp (x k)) (fun k => eSp (y k)) =
        (fun sigma : M => fun u => (sigma.val u : VH ⊕ VG)) ⁻¹' CylinderEvent x y := by
      ext sigma
      simp only [Set.mem_preimage, CylinderEvent, Set.mem_setOf_eq, heMSp, heKSp]
      exact ⟨fun hh k => eSp.injective (hh k), fun hh k => congrArg eSp (hh k)⟩
    exact eqset ▸ hh
  have hrawSub : VertexSpreadOn muf (P.certificate.matchingConstant round (exposure i) / m)
      Set.univ := by
    refine ⟨hrawAmb.1, ?_⟩
    intro s x y hxi _
    have h := hrawAmb.2 s x (fun k => (y k : VH ⊕ VG)) hxi (fun _ => Set.mem_univ _)
    rw [PMF.toOuterMeasure_map_apply] at h ⊢
    have hsets : (fun sigma : M => fun u => (sigma.val u : VH ⊕ VG)) ⁻¹'
        CylinderEvent x (fun k => (y k : VH ⊕ VG)) =
        Subtype.val ⁻¹' CylinderEvent x y := by
      ext sigma
      simp only [Set.mem_preimage, CylinderEvent, Set.mem_setOf_eq]
      exact ⟨fun hh k => Subtype.ext (hh k), fun hh k => congrArg Subtype.val (hh k)⟩
    exact hsets ▸ h
  have hraw : VertexSpreadOn muf (Cm / (2 * m)) Set.univ := by
    apply VertexSpreadMonotone hrawSub
    · rw [hCm2]
      calc
        P.certificate.matchingConstant round (exposure i) / m ≤ (C / 2) / m :=
          ENNReal.div_le_div_right (P.scalar_thresholds _ hx).2.2.2.2 _
        _ = C / (2 * m) := by rw [halve]; simp only [div_eq_mul_inv]; ac_rfl
        _ ≤ C / (2 * n) := by gcongr
    · simpa only [hCm2] using hhalfunit
  have hbudget : D * (1 - a) ^ m ≤ (2 : ENNReal)⁻¹ := by
    apply le_trans (mul_le_mul_left' (pow_le_pow_of_le_one (zero_le _) tsub_le_self hnm) _) P.local_loss
  have hgood (j : J) :
      1 - (1 - a) ^ m ≤ mu0.toOuterMeasure {sigma |
        letI : DecidableRel
            (MatchingInducedGraph (F13 j) (F23 j) U K (Z j) sigma).Adj := Classical.decRel _
        let L := Finset.univ.image (Sum.inl : U → U ⊕ Z j)
        let Q := Finset.univ.image (Sum.inr : Z j → U ⊕ Z j)
        SuperRegularPair (MatchingInducedGraph (F13 j) (F23 j) U K (Z j) sigma)
          L Q (omega (round + 1)) (rho (exposure j) * (d / 2))} := by
    let e4 := (Fintype.equivFin (VH ⊕ VG)).trans (Equiv.ulift.symm)
    obtain ⟨eU4, eK4, hUK4, eM4, heU4, heK4, heM4, hreg4, htrip4, hind4⟩ :=
      FiniteTripletRelabelling e4 F U K hUK
    let hM4 := hM.map eM4
    let mu4 := UniformPerfectMatching (F.comap e4.symm) (U.image e4) (K.image e4) hUK4 hM4
    have hg := P.certificate.fourGraphsGuarantee round P.round_bound
      (exposure i) (exposure j) hx (hy j).le
      (F.comap e4.symm) ((F13 j).comap e4.symm) ((F23 j).comap e4.symm)
      (U.image e4) (K.image e4) ((Z j).image e4) m
      ((P.ordered_thresholds _ _ hx (hy j).le).1.trans hnm)
      ((htrip4 _ _ _ _ _ _ _ _).mp (htrip j)) hUK4 hM4
    have uniform4 : mu0.map eM4 = mu4 := by
      letI := hM
      letI := hM4
      ext s
      rw [PMF.map_apply, ← eM4.symm.tsum_eq]
      simp only [eM4.apply_symm_apply, mu0, mu4, UniformPerfectMatching,
        PMF.uniformOfFintype_apply, Fintype.card_eq_nat_card, Nat.card_congr eM4]
      simp
    change _ ≤ mu4.toOuterMeasure _ at hg
    rw [← uniform4, PMF.toOuterMeasure_map_apply] at hg
    have hevent : eM4 ⁻¹' {sigma |
        letI : DecidableRel (MatchingInducedGraph ((F13 j).comap e4.symm)
          ((F23 j).comap e4.symm) (U.image e4) (K.image e4) ((Z j).image e4) sigma).Adj :=
          Classical.decRel _
        SuperRegularPair (MatchingInducedGraph ((F13 j).comap e4.symm)
          ((F23 j).comap e4.symm) (U.image e4) (K.image e4) ((Z j).image e4) sigma)
          (Finset.univ.image Sum.inl) (Finset.univ.image Sum.inr)
          (omega (round + 1)) (rho (exposure j) * (d / 2))} =
        {sigma : M |
          letI : DecidableRel (MatchingInducedGraph (F13 j) (F23 j) U K (Z j) sigma).Adj :=
            Classical.decRel _
          SuperRegularPair (MatchingInducedGraph (F13 j) (F23 j) U K (Z j) sigma)
            (Finset.univ.image Sum.inl) (Finset.univ.image Sum.inr)
            (omega (round + 1)) (rho (exposure j) * (d / 2))} := by
      ext sigma
      exact (hind4 (F13 j) (F23 j) (Z j) sigma _ _).symm
    rw [hevent] at hg
    apply le_trans ?_ hg
    apply tsub_le_tsub_left
    exact pow_le_pow_left' (tsub_le_tsub_left (P.ordered_thresholds _ _ hx (hy j).le).2 1) m
  obtain ⟨Ef, hEf, hmass, hEfSupport, hconditioned⟩ :=
    OneClusterExtension F F13 F23 U K Z m D (theta round) (rho (exposure i))
      (fun _ => theta round) (fun _ => omega (round + 1))
      (fun j => rho (exposure j)) (fun _ => d / 2) a Cm
      hJ hbudget (P.retained_density _ hx).1 (P.retained_density _ hx).2 hrho
      (by simpa only [hCm] using P.spread_unit) hU hK hF htrip hUK hM hraw hgood
  let E0 : Set M := Subtype.val ⁻¹' Ef
  have hE0 : ∃ sigma ∈ E0, sigma ∈ mu0.support := by
    obtain ⟨sigma, hs, hsup⟩ := hEfSupport
    obtain ⟨s, hsup, heq⟩ := (PMF.mem_support_map_iff Subtype.val mu0 sigma).mp hsup
    refine ⟨s, ?_, hsup⟩
    change s.val ∈ Ef
    rw [heq]
    exact hs
  let nu0 := mu0.map lift
  let E := lift '' E0
  have hE : ∃ g ∈ E, g ∈ nu0.support := by
    obtain ⟨s, hs, hsup⟩ := hE0
    exact ⟨lift s, ⟨s, hs, rfl⟩, (PMF.mem_support_map_iff _ _ _).mpr ⟨s, hsup, rfl⟩⟩
  have preE : lift ⁻¹' E = E0 := by
    ext s
    constructor
    · rintro ⟨s', hs', hh⟩
      exact lift.injective hh ▸ hs'
    · intro hs
      exact ⟨s, hs, rfl⟩
  -- Conditioning commutes with either pushforward along the same success preimage.
  have filter_map {α β : Type _} (p : PMF α) (b : α → β) (S : Set β)
      (hS : ∃ z ∈ S, z ∈ (p.map b).support)
      (hpre : ∃ z ∈ b ⁻¹' S, z ∈ p.support) :
      (p.filter (b ⁻¹' S) hpre).map b = (p.map b).filter S hS := by
    have hmass : (∑' z, ((b ⁻¹' S).indicator p) z) =
        ∑' z, (S.indicator (p.map b)) z := by
      simpa only [PMF.toOuterMeasure_apply] using (PMF.toOuterMeasure_map_apply b p S).symm
    ext z
    rw [PMF.map_apply, PMF.filter_apply, ← hmass]
    simp only [PMF.filter_apply]
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, PMF.map_apply, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases heq : z = b x
      · subst z
        simp [hz]
      · simp [heq]
    · simp only [Set.indicator_of_notMem hz, zero_mul]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      by_cases heq : z = b x
      · subst z
        simp [hz]
      · simp [heq]
  have commute0 : (mu0.filter E0 hE0).map Subtype.val = muf.filter Ef hEfSupport :=
    filter_map mu0 Subtype.val Ef hEfSupport hE0
  have commute : (mu0.filter E0 hE0).map lift = nu0.filter E hE := by
    have hp : ∃ s ∈ lift ⁻¹' E, s ∈ mu0.support := by simpa only [preE] using hE0
    simpa only [preE] using filter_map mu0 lift E hE hp
  -- Pull back cylinders through the source equivalence and the host injection.
  have transfer (p : PMF (U → K)) (Q : ENNReal) (hs : VertexSpreadOn p Q Set.univ) :
      VertexSpreadOn (p.map fun sigma => fun y : Y => v (sigma (e y))) Q Set.univ := by
    refine ⟨hs.1, ?_⟩
    intro s x y hxi _
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hall : ∀ k, ∃ z : K, v z = y k
    · choose z hz using hall
      have eqset : (fun sigma : U → K => fun y : Y => v (sigma (e y))) ⁻¹'
          CylinderEvent x y = CylinderEvent (fun k => e (x k)) z := by
        ext sigma
        exact ⟨fun h k => v.injective ((h k).trans (hz k).symm),
          fun h k => (congrArg v (h k)).trans (hz k)⟩
      rw [eqset]
      exact hs.2 s _ z (e.injective.comp hxi) (fun _ => Set.mem_univ _)
    · have hempty : (fun sigma : U → K => fun y : Y => v (sigma (e y))) ⁻¹'
          CylinderEvent x y = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro sigma hh
        exact hall (fun k => ⟨sigma (e (x k)), hh k⟩)
      simp [hempty, PMF.toOuterMeasure_apply]
  have rawEval : nu0.map (fun g => fun y : Y => g.toFun y.1) =
      muf.map (fun sigma => fun y : Y => v (sigma (e y))) := by
    simp only [nu0, muf, PMF.map_comp]
    congr 1
    funext sigma y
    exact hlift sigma y
  have condEval : (nu0.filter E hE).map (fun g => fun y : Y => g.toFun y.1) =
      (muf.filter Ef hEfSupport).map (fun sigma => fun y : Y => v (sigma (e y))) := by
    rw [← commute, ← commute0]
    simp only [PMF.map_comp]
    congr 1
    funext sigma y
    exact hlift sigma y
  refine ⟨nu0, E, hE, ?_, ?_, ?_, ?_⟩
  · rw [PMF.toOuterMeasure_map_apply, preE]
    rw [PMF.toOuterMeasure_map_apply] at hmass
    exact hmass
  · rw [rawEval]
    apply transfer
    simpa only [hCm2] using hraw
  · rw [condEval]
    apply transfer
    simpa only [hCm] using hconditioned
  · intro g hg h hxf hyg j hij hjS hjt
    obtain ⟨hgE, hgsup⟩ := (PMF.mem_support_filter_iff hE).mp hg
    obtain ⟨sigma, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hgsup
    have hsig : sigma.val ∈ Ef := by
      obtain ⟨s, hs, hh⟩ := hgE
      exact lift.injective hh ▸ hs
    let jj : J := ⟨j, hij, hjS, hjt⟩
    have hsuccess := (hEf sigma.val).mp hsig jj
    obtain ⟨W, hWT, hW⟩ := htransport sigma.val sigma.property.1 jj hsuccess
    obtain ⟨hTA, hL, hQ⟩ := hcontain sigma h hxf hyg j hij hjS hjt
    refine ⟨W, hWT.trans hTA, ?_⟩
    rw [hL, hQ]
    change @SuperRegularPair _ _ W (Classical.decRel _) _ _
      (epsilon (round + 1)) (density (exposure j + 1))
    rw [P.density_update (exposure j) (hy jj)]
    exact hW
