import Tablet.ColourRoundStepParameters
import Tablet.ColourRoundInvariant
import Tablet.ColourRoundUntouchedGeometry
import Tablet.InstanceSuperRegular
import Tablet.SaturatingSourcePair
import Tablet.EqualSizeSourceWitnessTransport
import Tablet.CurrentExtraSourceWitnessTransport
import Tablet.FutureExtraSourceWitnessTransport
import Tablet.NearEqualVaryingGoodEdgeSuperRegularity
import Tablet.FiniteTripletRelabelling
import Tablet.ColourRoundWitnessThinnings
import Tablet.ColourRoundSourceWitnessAssembly

-- [TABLET NODE: ColourRoundRetainedTriplets]
theorem ColourRoundRetainedTriplets
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
    (hn : 1 ≤ n)
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
    let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
    let K0 := Finset.univ.filter fun v : VG => B.hostCluster v = i
    let U := Y.image (Sum.inl : VH → VH ⊕ VG)
    let K := K0.image (Sum.inr : VG → VH ⊕ VG)
    let J := {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val}
    let Z : J → Finset (VH ⊕ VG) := fun j =>
      (Finset.univ.filter fun v : VG => B.hostCluster v = j).image Sum.inr
    let exposure := fun j : Fin r => (Finset.univ.filter fun k : Fin r =>
      ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
    let Ai := SimpleGraph.fromRel fun p s =>
      ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
        (y, v) ∈ UpdatedCandidacyCluster B A X f i
    ∃ (F : SimpleGraph (VH ⊕ VG)) (F13 F23 : J → SimpleGraph (VH ⊕ VG)),
      F ≤ Ai ∧
      @SuperRegularPair _ _ F (Classical.decRel _) U K (theta round) (rho (exposure i)) ∧
      (∀ j, @NearEqualRegularTriplet _ _ _ F (F13 j) (F23 j)
        (Classical.decRel _) (Classical.decRel _) (Classical.decRel _)
        U K (Z j) Y.card (theta round) (rho (exposure i))
          (rho (exposure j)) (d / 2)) ∧
      (∀ sigma : U → K, Function.Bijective sigma → ∀ j : J,
        let I := @MatchingInducedGraph _ _ _ (F13 j) (F23 j)
          (Classical.decRel _) (Classical.decRel _) U K (Z j) sigma
        let L := Finset.univ.image (Sum.inl : U → U ⊕ Z j)
        let Q := Finset.univ.image (Sum.inr : Z j → U ⊕ Z j)
        @SuperRegularPair _ _ I (Classical.decRel _) L Q
          (omega (round + 1)) (rho (exposure j) * (d / 2)) →
        let Vj := (Finset.univ.filter fun y : VH => B.sourceCluster y = j).image
          (Sum.inl : VH → VH ⊕ VG)
        let T := SimpleGraph.fromRel fun p s =>
          ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
            (y, v) ∈ UpdatedCandidacyCluster B A X f j ∧
            ∀ u : U, (∃ x : VH, (u : VH ⊕ VG) = Sum.inl x ∧ H.Adj x y) →
              ∃ w : VG, (sigma u : VH ⊕ VG) = Sum.inr w ∧ G.Adj w v
        ∃ W : SimpleGraph (VH ⊕ VG), W ≤ T ∧
          @SuperRegularPair _ _ W (Classical.decRel _) Vj (Z j)
            (epsilon (round + 1)) (rho (exposure j) * (d / 2))) := by
-- BODY
  classical
  dsimp only
  let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
  let K0 := Finset.univ.filter fun v : VG => B.hostCluster v = i
  let U := Y.image (Sum.inl : VH → VH ⊕ VG)
  let K := K0.image (Sum.inr : VG → VH ⊕ VG)
  let J := {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val}
  let Z : J → Finset (VH ⊕ VG) := fun j =>
    (Finset.univ.filter fun v : VG => B.hostCluster v = j).image Sum.inr
  let exposure := fun j : Fin r => (Finset.univ.filter fun k : Fin r =>
    ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
  let Ai := SimpleGraph.fromRel fun p s =>
    ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
      (y, v) ∈ UpdatedCandidacyCluster B A X f i
  obtain ⟨heI, heJ, W12, O, W13, W23, hsub, h12, hfamily⟩ :=
    ColourRoundWitnessThinnings B A colour theta density epsilon rho eta omega xi
      D d C a n round P hsizes hhost touched X mu hinv i hi hiS f hf
  have prepared (j : J) := ColourRoundSourceWitnessAssembly B A
    theta density epsilon rho eta omega xi D d C a n round (exposure j) P hn
    (heJ j) i j j.property.1 (hsource j.property.1) hsizes X f
    (O j) (W13 j) (W23 j) (hfamily j).1 (hfamily j).2.2.1
    (hfamily j).2.2.2.2.1 (hfamily j).2.1 (hfamily j).2.2.2.1
  choose F13 h13 htransport using prepared
  letI : DecidableRel W12.Adj := Classical.decRel _
  letI : ∀ j, DecidableRel (F13 j).Adj := fun _ => Classical.decRel _
  letI : ∀ j, DecidableRel (W23 j).Adj := fun _ => Classical.decRel _
  have enlarge (T : SimpleGraph (VH ⊕ VG)) [DecidableRel T.Adj]
      (L Q : Finset (VH ⊕ VG)) (b c p : ENNReal) (hbc : b ≤ c)
      (hT : SuperRegularPair T L Q b p) : SuperRegularPair T L Q c p := by
    as_aux_lemma =>
      refine ⟨?_, ?_, ?_⟩
      · intro S hS T hT' hs ht
        obtain ⟨hl, hu⟩ := hT.1 S hS T hT'
          (lt_of_le_of_lt (mul_le_mul_left hbc _) hs)
          (lt_of_le_of_lt (mul_le_mul_left hbc _) ht)
        exact ⟨(tsub_le_tsub_left hbc p).trans hl,
          hu.trans (add_le_add_right hbc p)⟩
      · intro x hx
        exact ⟨(mul_le_mul_left (tsub_le_tsub_left hbc p) _).trans (hT.2.1 x hx).1,
          (hT.2.1 x hx).2.trans (mul_le_mul_left (add_le_add_right hbc p) _)⟩
      · intro y hy
        exact ⟨(mul_le_mul_left (tsub_le_tsub_left hbc p) _).trans (hT.2.2 y hy).1,
          (hT.2.2 y hy).2.trans (mul_le_mul_left (add_le_add_right hbc p) _)⟩
  have hUK : Disjoint U K := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzK
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzU
    obtain ⟨v, _, he⟩ := Finset.mem_image.mp hzK
    cases he
  have hdisj (j : J) : Disjoint U (Z j) ∧ Disjoint K (Z j) := by
    constructor
    · apply Finset.disjoint_left.mpr
      intro z hzU hzZ
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzU
      obtain ⟨v, _, he⟩ := Finset.mem_image.mp hzZ
      cases he
    · apply Finset.disjoint_left.mpr
      intro z hzK hzZ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hzK
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hzZ
      have he' := Sum.inr_injective he
      subst w
      exact R.ne_of_adj j.property.1
        (((Finset.mem_filter.mp hv).2).symm.trans (Finset.mem_filter.mp hw).2)
  have hU : U.card = Y.card := Finset.card_image_of_injective _ Sum.inl_injective
  have hK : K.card = Y.card := by
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    exact (hsizes i).2.symm
  have hnear (j : J) : (Z j).card + 1 = Y.card ∨
      (Z j).card = Y.card ∨ (Z j).card = Y.card + 1 := by
    have hz : (Z j).card =
        (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card := by
      rw [Finset.card_image_of_injective _ Sum.inr_injective]
      exact (hsizes j).2.symm
    rw [hz]
    rcases (hsizes i).1 with hi' | hi' <;>
      rcases (hsizes j).1 with hj' | hj' <;> simp only [Y] at * <;> omega
  have htests : Fintype.card J ≤ D := by
    calc
      Fintype.card J ≤ Fintype.card {j : Fin r // R.Adj i j} :=
        Fintype.card_le_of_injective
          (fun j : J => (⟨j.val, j.property.1⟩ : {j : Fin r // R.Adj i j}))
          (fun _ _ he => Subtype.ext (congrArg (fun j : {j : Fin r // R.Adj i j} => j.val) he))
      _ = (Finset.univ.filter fun j => R.Adj i j).card := by
        exact (Fintype.card_subtype _).trans rfl
      _ ≤ D := hinv.2.1 i
  have htwo : eta round ≤ 2 * eta round := by
    calc
      eta round ≤ eta round + eta round := le_add_right le_rfl
      _ = 2 * eta round := by ring
  have heta : eta round ≤ 1 :=
    htwo.trans ((P.host_density_upper.le).trans tsub_le_self)
  have hetheta : eta round ≤ theta round :=
    (le_add_right le_rfl).trans P.degree_loss
  have hwindow : 2 * eta round ≤ theta round := by
    have hsqrt : eta round ≤ (eta round) ^ (2 : ℝ)⁻¹ := by
      simpa only [ENNReal.rpow_one] using
        (ENNReal.rpow_le_rpow_of_exponent_ge heta (by norm_num : (2 : ℝ)⁻¹ ≤ 1))
    exact (mul_le_mul_right hsqrt 2).trans P.square_root_loss
  have hp (x : ℕ) (hx : x ≤ D) : rho x ≤ 1 := by
    have hh := (P.witness_density x hx).2
    have hlt : 0 < 1 - rho x := (zero_le _).trans_lt hh
    exact (tsub_pos_iff_lt.mp hlt).le
  have hd : d / 2 ≤ 1 := by
    have hh : 0 < 1 - d / 2 := (zero_le _).trans_lt P.host_density_upper
    exact (tsub_pos_iff_lt.mp hh).le
  have h23 (j : J) : SuperRegularPair (W23 j) K (Z j) (eta round) (d / 2) :=
    enlarge _ _ _ _ _ _ P.inner_reserve.le (hfamily j).2.2.2.2.2
  have hsum (b : ENNReal) : (∑ _j : J, b) ≤ D * b := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_le_mul_left (by exact_mod_cast htests) b
  let F := SimultaneousGoodEdgeGraph W12 F13 W23 U K hUK Z
    (fun _ => eta round) (fun j => rho (exposure j)) (fun _ => d / 2)
  letI : DecidableRel F.Adj := Classical.decRel _
  have hF : SuperRegularPair F U K (theta round) (rho (exposure i)) :=
    NearEqualVaryingGoodEdgeSuperRegularity W12 F13 W23 U K Z Y.card
      (eta round) (theta round) (rho (exposure i)) (fun _ => eta round)
      (fun j => rho (exposure j)) (fun _ => d / 2) hUK hdisj hU hK hnear
      hetheta (fun _ => ⟨heta, P.square_root_loss⟩)
      ((add_le_add le_rfl (hsum ((eta round) ^ (2 : ℝ)⁻¹))).trans P.regularity_loss)
      ((add_le_add le_rfl (mul_le_mul_right (hsum (eta round)) 2)).trans
        (by simpa only [mul_assoc] using P.degree_loss))
      (fun j => ⟨(P.witness_density _ (heJ j).le).1, P.host_density_lower⟩)
      (fun j => ⟨hp _ (heJ j).le, hd⟩)
      (enlarge _ _ _ _ _ _ P.inner_reserve.le h12) h13 h23
  refine ⟨F, F13, W23, ?_, hF, ?_, fun sigma hs j => htransport j sigma hs⟩
  · intro x v hxv
    obtain ⟨_, hh | hh⟩ := hxv
    · exact hsub hh.2.2.1
    · exact (hsub hh.2.2.1).symm
  · intro j
    refine ⟨hU, hK, hnear j, hUK, (hdisj j).1, (hdisj j).2, hF,
      enlarge _ _ _ _ _ _ hetheta (h13 j),
      enlarge _ _ _ _ _ _ hetheta (h23 j), ?_⟩
    intro x hx v hv hxv
    have hh :
        (rho (exposure j) * (d / 2) - 2 * eta round) * (Z j).card ≤
          (((Z j).filter fun z => (F13 j).Adj x z ∧ (W23 j).Adj v z).card : ENNReal) ∧
        (((Z j).filter fun z => (F13 j).Adj x z ∧ (W23 j).Adj v z).card : ENNReal) ≤
          (rho (exposure j) * (d / 2) + 2 * eta round) * (Z j).card := by
      obtain ⟨_, hh | hh⟩ := hxv
      · exact hh.2.2.2 j
      · exact False.elim (Finset.disjoint_left.mp hUK hh.1 hv)
    exact ⟨(mul_le_mul_left (tsub_le_tsub_left hwindow _) _).trans hh.1,
      hh.2.trans (mul_le_mul_left (add_le_add_right hwindow _) _)⟩
