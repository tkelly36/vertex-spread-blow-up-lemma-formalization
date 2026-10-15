import Tablet.ColourRoundStepParameters
import Tablet.ColourRoundInvariant
import Tablet.ColourRoundUntouchedGeometry
import Tablet.InstanceSuperRegular
import Tablet.FiniteSuperRegularThinning
import Tablet.SuperRegularPairEmbedding

-- [TABLET NODE: ColourRoundWitnessThinnings]
theorem ColourRoundWitnessThinnings
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
    (touched : Finset (Fin r)) (X : Finset VH)
    (mu : PMF (PartialCompatibleEmbedding B A X))
    (hinv : ColourRoundInvariant B A colour epsilon density D C n round touched X mu)
    (i : Fin r) (hi : (colour i).val = round) (hiS : i ∉ touched)
    (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) :
    let L := fun j : Fin r =>
      (Finset.univ.filter fun x : VH => B.sourceCluster x = j).image
        (Sum.inl : VH → VH ⊕ VG)
    let Q := fun j : Fin r =>
      (Finset.univ.filter fun v : VG => B.hostCluster v = j).image
        (Sum.inr : VG → VH ⊕ VG)
    let J := {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val}
    let exposure := fun j : Fin r => (Finset.univ.filter fun k : Fin r =>
      ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
    let Aj := fun j : Fin r => SimpleGraph.fromRel fun p s =>
      ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
        (y, v) ∈ UpdatedCandidacyCluster B A X f j
    let H0 : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
      ∃ v w : VG, p = Sum.inr v ∧ s = Sum.inr w ∧ G.Adj v w
    exposure i ≤ D ∧ (∀ j : J, exposure j < D) ∧
    ∃ (W12 : SimpleGraph (VH ⊕ VG))
      (O W13 W23 : J → SimpleGraph (VH ⊕ VG)),
      W12 ≤ Aj i ∧
      @SuperRegularPair _ _ W12 (Classical.decRel _) (L i) (Q i)
        (xi round) (rho (exposure i)) ∧
      (∀ j, O j ≤ Aj j ∧
        @SuperRegularPair _ _ (O j) (Classical.decRel _) (L j) (Q j)
          (epsilon round) (density (exposure j)) ∧
        W13 j ≤ O j ∧
        @SuperRegularPair _ _ (W13 j) (Classical.decRel _) (L j) (Q j)
          (xi round) (rho (exposure j)) ∧
        W23 j ≤ H0 ∧
        @SuperRegularPair _ _ (W23 j) (Classical.decRel _) (Q i) (Q j)
          (xi round) (d / 2)) := by
-- BODY
  classical
  dsimp only
  let L := fun j : Fin r =>
    (Finset.univ.filter fun x : VH => B.sourceCluster x = j).image
      (Sum.inl : VH → VH ⊕ VG)
  let Q := fun j : Fin r =>
    (Finset.univ.filter fun v : VG => B.hostCluster v = j).image
      (Sum.inr : VG → VH ⊕ VG)
  let J := {j : Fin r // R.Adj i j ∧ j ∉ touched ∧ round ≤ (colour j).val}
  let exposure := fun j : Fin r => (Finset.univ.filter fun k : Fin r =>
    ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
  let Aj := fun j : Fin r => SimpleGraph.fromRel fun p s =>
    ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
      (y, v) ∈ UpdatedCandidacyCluster B A X f j
  let H0 : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
    ∃ v w : VG, p = Sum.inr v ∧ s = Sum.inr w ∧ G.Adj v w
  obtain ⟨_, hdegree, hcolour, htouched, hX, _, hwitness⟩ := hinv
  obtain ⟨hcurrent, hfuture, _, hstrict⟩ :=
    ColourRoundUntouchedGeometry R colour D round touched i hdegree hcolour htouched hi hiS
  have absent (j : Fin r) (hj : j ∉ touched) (hc : round ≤ (colour j).val)
      (x : VH) (hx : B.sourceCluster x = j) : x ∉ X := by
    rw [hX]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx]
    exact not_or.mpr ⟨not_lt.mpr hc, hj⟩
  have unused (j : Fin r) (hj : j ∉ touched) (hc : round ≤ (colour j).val)
      (v : VG) (hv : B.hostCluster v = j) : v ∉ X.image f.toFun := by
    intro hused
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hused
    have hcluster := A.cluster_respecting (f.compatible x hx)
    exact absent j hj hc x (hcluster.trans (he ▸ hv)) hx
  have disj (j : Fin r) : Disjoint (L j) (Q j) := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzQ
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hzL
    obtain ⟨v, _, he⟩ := Finset.mem_image.mp hzQ
    cases he
  have cardL (j : Fin r) : (L j).card =
      (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have cardQ (j : Fin r) : (Q j).card =
      (Finset.univ.filter fun v : VG => B.hostCluster v = j).card :=
    Finset.card_image_of_injective _ Sum.inr_injective
  have witness (j : Fin r) (hj : j ∉ touched) (hc : round ≤ (colour j).val)
      (ht : (touched.filter fun k => R.Adj j k) = ∅) :
      exposure j ≤ D ∧ ∃ O : SimpleGraph (VH ⊕ VG), O ≤ Aj j ∧
        @SuperRegularPair _ _ O (Classical.decRel _) (L j) (Q j)
          (epsilon round) (density (exposure j)) := by
    obtain ⟨he, _, O, hO, hsr⟩ := hwitness f hf j hj hc
    have heL : (Finset.univ.filter fun z : VH ⊕ VG =>
        ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X) = L j := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, L, Finset.mem_image]
      constructor
      · rintro ⟨y, rfl, hy, _⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, rfl, hy, absent j hj hc y hy⟩
    have heQ : (Finset.univ.filter fun z : VH ⊕ VG =>
        ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧
          v ∉ X.image f.toFun) = Q j := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, Finset.mem_image]
      constructor
      · rintro ⟨v, rfl, hv, _⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, rfl, hv, by simpa only [Finset.mem_image] using unused j hj hc v hv⟩
    refine ⟨he, O, hO, ?_⟩
    simpa only [heL, heQ, ht, Finset.not_nonempty_empty, if_false] using hsr
  have thin (j : Fin r) (hj : j ∉ touched) (hc : round ≤ (colour j).val)
      (ht : (touched.filter fun k => R.Adj j k) = ∅) :
      exposure j ≤ D ∧ ∃ O W : SimpleGraph (VH ⊕ VG), O ≤ Aj j ∧
        @SuperRegularPair _ _ O (Classical.decRel _) (L j) (Q j)
          (epsilon round) (density (exposure j)) ∧
        W ≤ O ∧ @SuperRegularPair _ _ W (Classical.decRel _) (L j) (Q j)
          (xi round) (rho (exposure j)) := by
    obtain ⟨he, O, hO, hsr⟩ := witness j hj hc ht
    letI : DecidableRel O.Adj := Classical.decRel _
    have hsize : n ≤ (L j).card := by rw [cardL]; rcases (hsizes j).1 with h | h <;> omega
    have hsame : (L j).card = (Q j).card := by rw [cardL, cardQ]; exact (hsizes j).2
    have hN := (P.scalar_thresholds (exposure j) he).1
    obtain ⟨W, hWO, hW⟩ := FiniteSuperRegularThinning
      _ _ _ _ _ (P.certificate.witnessThinningGuarantee round P.round_bound (exposure j) he)
      O (L j) (Q j) (disj j) (hN.trans hsize)
      (by simpa only [← hsame] using hN.trans hsize)
      (by omega) (by omega) hsr
    exact ⟨he, O, W, hO, hsr, hWO, hW⟩
  obtain ⟨heI, Oi, W12, hOi, _, hWi, hW12⟩ := thin i hiS (by omega) hcurrent
  have host (j : J) : ∃ W : SimpleGraph (VH ⊕ VG), W ≤ H0 ∧
      @SuperRegularPair _ _ W (Classical.decRel _) (Q i) (Q j)
        (xi round) (d / 2) := by
    let Vi := Finset.univ.filter fun v : VG => B.hostCluster v = i
    let Vj := Finset.univ.filter fun v : VG => B.hostCluster v = j.val
    have hd : Disjoint Vi Vj := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact R.ne_of_adj j.property.1
        (((Finset.mem_filter.mp hv).2).symm.trans (Finset.mem_filter.mp hw).2)
    have hsi : Vi.card = n ∨ Vi.card = n + 1 := by
      simpa only [(hsizes i).2] using (hsizes i).1
    have hsj : Vj.card = n ∨ Vj.card = n + 1 := by
      simpa only [(hsizes j).2] using (hsizes j).1
    have hN := (P.scalar_thresholds (exposure i) heI).2.1
    obtain ⟨T, hTG, hT⟩ := FiniteSuperRegularThinning
      _ _ _ _ _ (P.certificate.hostThinningGuarantee round P.round_bound)
      G Vi Vj hd (by rcases hsi with h | h <;> omega)
      (by rcases hsj with h | h <;> omega)
      (by rcases hsi with h | h <;> rcases hsj with h' | h' <;> omega)
      (by rcases hsi with h | h <;> rcases hsj with h' | h' <;> omega)
      (hhost j.property.1)
    let W : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
      ∃ v w : VG, p = Sum.inr v ∧ s = Sum.inr w ∧ T.Adj v w
    letI : DecidableRel T.Adj := Classical.decRel _
    letI : DecidableRel W.Adj := Classical.decRel _
    have adj (v w : VG) : W.Adj (Sum.inr v) (Sum.inr w) ↔ T.Adj v w := by
      simp only [W, SimpleGraph.fromRel_adj, Sum.inr.injEq]
      constructor
      · rintro ⟨_, hh | hh⟩
        · obtain ⟨v', w', rfl, rfl, hh⟩ := hh; exact hh
        · obtain ⟨v', w', rfl, rfl, hh⟩ := hh; exact hh.symm
      · intro hh
        exact ⟨fun he => T.ne_of_adj hh (Sum.inr_injective he),
          Or.inl ⟨v, w, rfl, rfl, hh⟩⟩
    refine ⟨W, ?_, ?_⟩
    · intro p s hps
      obtain ⟨hne, hh | hh⟩ := hps
      · obtain ⟨v, w, rfl, rfl, hh⟩ := hh
        exact ⟨hne, Or.inl ⟨v, w, rfl, rfl, hTG hh⟩⟩
      · obtain ⟨v, w, rfl, rfl, hh⟩ := hh
        exact ⟨hne, Or.inr ⟨v, w, rfl, rfl, hTG hh⟩⟩
    · exact SuperRegularPairEmbedding Sum.inr Sum.inr_injective T W Vi Vj
        _ _ (fun v _ w _ => adj v w) hT
  have each (j : J) : ∃ O W13 W23 : SimpleGraph (VH ⊕ VG),
      O ≤ Aj j ∧ @SuperRegularPair _ _ O (Classical.decRel _) (L j) (Q j)
        (epsilon round) (density (exposure j)) ∧
      W13 ≤ O ∧ @SuperRegularPair _ _ W13 (Classical.decRel _) (L j) (Q j)
        (xi round) (rho (exposure j)) ∧
      W23 ≤ H0 ∧ @SuperRegularPair _ _ W23 (Classical.decRel _) (Q i) (Q j)
        (xi round) (d / 2) := by
    obtain ⟨_, O, W13, hO, hsr, hsub, hW⟩ :=
      thin j j.property.2.1 j.property.2.2 (hfuture j j.property.1)
    obtain ⟨W23, hsub23, h23⟩ := host j
    exact ⟨O, W13, W23, hO, hsr, hsub, hW, hsub23, h23⟩
  choose O W13 W23 hfamily using each
  exact ⟨heI, fun j => (hstrict j j.property.1).1,
    W12, O, W13, W23, hWi.trans hOi, hW12, hfamily⟩
