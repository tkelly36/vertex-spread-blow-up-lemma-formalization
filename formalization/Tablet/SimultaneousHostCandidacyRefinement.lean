import Tablet.BlowUpInstance
import Tablet.CandidacySystem
import Tablet.CandidacyLowerSuperRegular
import Tablet.CandidacySuperRegular
import Tablet.InstanceLowerSuperRegular
import Tablet.InstanceSuperRegular
import Tablet.LowerRegularPair
import Tablet.LowerSuperRegularPair
import Tablet.PairDensity
import Tablet.RegularPair
import Tablet.SuperRegularPair
import Tablet.SuperRegularSubgraph
import Tablet.NearEqualSuperRegularExtraction
import Tablet.HostRefinementParameters
import Tablet.PrescribedHostPartitionSample
import Tablet.HostExceptionalCorrection
import Tablet.RefinedLowerSuperRegularTransfer
import Tablet.CrossPairSubgraphAssembly
import Tablet.TaggedCandidacyAssembly

-- [TABLET NODE: SimultaneousHostCandidacyRefinement]
theorem SimultaneousHostCandidacyRefinement :
    ∀ (Delta : ℕ) (ε' d' d : ENNReal), 1 ≤ Delta → 0 < ε' → ε' < 1 →
      0 < d' → d' < d ^ 2 / 2 → d ≤ 1 →
      ∃ ε : ENNReal, 0 < ε ∧ ε < ε' ∧
      ∀ r : ℕ, ∃ n₀ : ℕ,
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {VH VG : Type*} [Fintype VH] [Fintype VG]
        [DecidableEq VH] [DecidableEq VG]
        {H H' : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
        {R' : SimpleGraph (Fin r × Fin (Delta ^ 2))}
        [DecidableRel H.Adj] [DecidableRel H'.Adj] [DecidableRel G.Adj]
        [DecidableRel R.Adj] [DecidableRel R'.Adj]
        (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
        (B₀ : BlowUpInstance (r * Delta ^ 2) VH VG H' G
          (R'.comap finProdFinEquiv.symm)),
        (∀ i,
          (Finset.univ.filter fun x : VH => B.sourceCluster x = i).card = n ∧
          (Finset.univ.filter fun v : VG => B.hostCluster v = i).card = n) →
        H ≤ H' →
        (∀ x, (finProdFinEquiv.symm (B₀.sourceCluster x)).1 = B.sourceCluster x) →
        (∀ p q, R'.Adj p q → R.Adj p.1 q.1) →
        (∀ p,
          let s := Finset.univ.filter fun x : VH => B₀.sourceCluster x = finProdFinEquiv p
          s.card = n / (Delta ^ 2) ∨ s.card = n / (Delta ^ 2) + 1) →
        InstanceLowerSuperRegular B ε d → CandidacyLowerSuperRegular B A ε d →
        ∃ (G' : SimpleGraph VG) (_ : DecidableRel G'.Adj)
          (B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G'
            (R'.comap finProdFinEquiv.symm)) (A' : CandidacySystem B'),
          G' ≤ G ∧
          (∀ x, B'.sourceCluster x = B₀.sourceCluster x) ∧
          (∀ v, (finProdFinEquiv.symm (B'.hostCluster v)).1 = B.hostCluster v) ∧
          (∀ {x v}, A'.allowed x v → A.allowed x v) ∧
          (∀ p,
            let X := Finset.univ.filter fun x : VH => B'.sourceCluster x = finProdFinEquiv p
            let V := Finset.univ.filter fun v : VG => B'.hostCluster v = finProdFinEquiv p
            X.card = V.card ∧
              (X.card = n / (Delta ^ 2) ∨ X.card = n / (Delta ^ 2) + 1)) ∧
          InstanceSuperRegular B' ε' d' ∧ CandidacySuperRegular B' A' ε' d' := by
-- BODY
  classical
  intro Delta η c d hDelta hη hη1 hc hcd hd1
  obtain ⟨θ, N, hθ, hθη, hN, hextract, hextractCand⟩ :=
    NearEqualSuperRegularExtraction η c d hη hη1 hc hcd hd1
  have hηfin : η ≠ ⊤ := ne_top_of_lt hη1
  have hθ1 : θ < 1 := hθη.trans hη1
  have hθfin : θ ≠ ⊤ := ne_top_of_lt hθ1
  have hk : 1 ≤ Delta ^ 2 := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  have hηR : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηfin
  have hηR1 : η.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hηfin (by simp)).mpr hη1
  have hθR : 0 < θ.toReal := ENNReal.toReal_pos hθ.ne' hθfin
  obtain ⟨e, he, heη, he1, heksmall, heθ, hethreshold, horders⟩ :=
    HostRefinementParameters (Delta ^ 2) N η.toReal θ.toReal hk hηR hηR1 hθR
  let ε := ENNReal.ofReal e
  have hε : 0 < ε := ENNReal.ofReal_pos.mpr he
  have hεη : ε < η := (ENNReal.ofReal_lt_iff_lt_toReal he.le hηfin).mpr heη
  have hε1 : ε < 1 := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr he1
  have hεsmall : ε < 1 / (8 * (Delta ^ 2 : ℕ) ^ 2 : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (by simp [ε]) (by finiteness)).mp
    simpa only [ε, ENNReal.toReal_ofReal he.le, ENNReal.toReal_div,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] using heksmall
  have hsmall : (4 * ((Delta ^ 2 : ℕ) : ENNReal) ^ 2 + 2) * ε ≤ θ := by
    apply (ENNReal.toReal_le_toReal (by finiteness) hθfin).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
    simpa only [ε, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal he.le,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat] using heθ
  have hthreshold : 2 * ((Delta ^ 2 : ℕ) : ENNReal) * ε ≤ θ := by
    apply (ENNReal.toReal_le_toReal (by finiteness) hθfin).mp
    simpa only [ε, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal he.le, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] using hethreshold
  refine ⟨ε, hε, hεη, ?_⟩
  intro r
  obtain ⟨n₀, hn₀⟩ := horders r
  refine ⟨n₀, ?_⟩
  intro n hn VH VG _ _ _ _ H H' G R R' _ _ _ _ _ B A B₀
    hcard hHH' hσproj hRproj hsize hhost hcand
  obtain ⟨hn2, hnN, htailR⟩ := hn₀ n hn
  by_cases hr : r = 0
  · subst r
    let G' : SimpleGraph VG := ⊥
    letI : DecidableRel G'.Adj := Classical.decRel _
    let B' : BlowUpInstance (0 * Delta ^ 2) VH VG H' G'
        (R'.comap finProdFinEquiv.symm) := {
      sourceCluster := B₀.sourceCluster
      hostCluster := B₀.hostCluster
      source_independent := B₀.source_independent
      capacity := B₀.capacity
      reduced_support := B₀.reduced_support }
    let A' : CandidacySystem B' := {
      allowed := fun _ _ => False
      cluster_respecting := fun h => h.elim }
    refine ⟨G', inferInstance, B', A', bot_le, (fun _ => rfl), ?_, ?_, ?_, ?_, ?_⟩
    · intro v
      exact (B.hostCluster v).elim0
    · intro x v h
      exact h.elim
    · intro p
      exact p.1.elim0
    · intro i j h
      exact (finProdFinEquiv.symm i).1.elim0
    · intro i
      exact (finProdFinEquiv.symm i).1.elim0
  let σ : VH → Fin r × Fin (Delta ^ 2) := fun x => finProdFinEquiv.symm (B₀.sourceCluster x)
  have hXeq (p : Fin r × Fin (Delta ^ 2)) :
      (Finset.univ.filter fun x => σ x = p) =
        (Finset.univ.filter fun x => B₀.sourceCluster x = finProdFinEquiv p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ,
      finProdFinEquiv.symm_apply_eq]
  have hsizeσ (p : Fin r × Fin (Delta ^ 2)) :
      (Finset.univ.filter fun x => σ x = p).card = n / (Delta ^ 2) ∨
      (Finset.univ.filter fun x => σ x = p).card = n / (Delta ^ 2) + 1 := by
    simpa only [hXeq] using hsize p
  have htail : 2 * (r : ℝ) * (Delta ^ 2 : ℕ) * (r + 1) * n *
      Real.exp (-((ε.toReal / (2 * (Delta ^ 2 : ℕ))) ^ 2 /
        (2 * (1 + ε.toReal / (6 * (Delta ^ 2 : ℕ))))) * n) < 1 := by
    simpa only [ε, ENNReal.toReal_ofReal he.le] using htailR
  obtain ⟨f, hf, hcapacity, hsource, hhostdegree⟩ :=
    PrescribedHostPartitionSample B A σ ε d n hk hn2 hε hε1 hd1
      hσproj hcard hsizeσ hhost hcand htail
  obtain ⟨f', hf', hcapacity', hchange, hcandidatedegree⟩ :=
    HostExceptionalCorrection B A σ f ε d n hk hn2 hε hεsmall hd1
      hσproj hf hcard hsizeσ hcapacity hcand
  obtain ⟨hhostlow, hcandlow⟩ := RefinedLowerSuperRegularTransfer B A σ f f' ε θ d n
    hk hn2 hθ1 hsmall hthreshold hσproj hf hf' hcard hsizeσ
    hcapacity hcapacity' hchange hsource hhostdegree hcandidatedegree hhost hcand
  have hhostsize (p : Fin r × Fin (Delta ^ 2)) :
      (Finset.univ.filter fun v => f' v = p).card = n / (Delta ^ 2) ∨
      (Finset.univ.filter fun v => f' v = p).card = n / (Delta ^ 2) + 1 := by
    rw [hcapacity' p]
    exact hsizeσ p
  have hhostextract : ∀ p q, R'.Adj p q →
      ∃ F : SimpleGraph VG, ∃ _ : DecidableRel F.Adj,
        F ≤ G ∧ (∀ ⦃u v⦄, F.Adj u v →
          (f' u = p ∧ f' v = q) ∨ (f' u = q ∧ f' v = p)) ∧
        SuperRegularPair F (Finset.univ.filter fun v => f' v = p)
          (Finset.univ.filter fun v => f' v = q) η c := by
    intro p q hpq
    have hdis : Disjoint (Finset.univ.filter fun v => f' v = p)
        (Finset.univ.filter fun v => f' v = q) := by
      apply Finset.disjoint_left.mpr
      intro v hvp hvq
      have hpqeq := (Finset.mem_filter.mp hvp).2.symm.trans (Finset.mem_filter.mp hvq).2
      exact R'.ne_of_adj hpq hpqeq
    obtain ⟨F, hFdec, hFG, hFcross, hFreg⟩ := hextract G _ _ (n / (Delta ^ 2)) hnN
      hdis (hhostsize p) (hhostsize q) (hhostlow p q (hRproj p q hpq))
    refine ⟨F, hFdec, hFG, ?_, hFreg⟩
    intro u v huv
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hFcross huv
  obtain ⟨G', hG'dec, hG'G, hG'support, hG'reg⟩ :=
    CrossPairSubgraphAssembly G R' f' η c hhostextract
  letI := hG'dec
  have hVeq (j : Fin (r * Delta ^ 2)) :
      (Finset.univ.filter fun v => finProdFinEquiv (f' v) = j) =
        (Finset.univ.filter fun v => f' v = finProdFinEquiv.symm j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      finProdFinEquiv.apply_eq_iff_eq_symm_apply]
  let B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G'
      (R'.comap finProdFinEquiv.symm) := {
    sourceCluster := B₀.sourceCluster
    hostCluster := fun v => finProdFinEquiv (f' v)
    source_independent := B₀.source_independent
    capacity := by
      intro j
      change Fintype.card {x : VH // B₀.sourceCluster x = j} ≤
        Fintype.card {v : VG // finProdFinEquiv (f' v) = j}
      simp only [Fintype.card_subtype, hVeq, hcapacity', hXeq,
        finProdFinEquiv.apply_symm_apply]
      exact le_rfl
    reduced_support := B₀.reduced_support }
  have hcandextract : ∀ j : Fin (r * Delta ^ 2),
      let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ x, z = Sum.inl x ∧ B'.sourceCluster x = j
      let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ v, z = Sum.inr v ∧ B'.hostCluster v = j
      let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
        ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A.allowed x v
      ∃ F : SimpleGraph (VH ⊕ VG), ∃ _ : DecidableRel F.Adj,
        F ≤ C ∧ SuperRegularPair F L Q η c := by
    intro j
    let p := finProdFinEquiv.symm j
    let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z => ∃ x, z = Sum.inl x ∧ σ x = p
    let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z => ∃ v, z = Sum.inr v ∧ f' v = p
    let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
      ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A.allowed x v
    letI : DecidableRel C.Adj := Classical.decRel _
    have hLmap : L = (Finset.univ.filter fun x => σ x = p).map
        ⟨Sum.inl, Sum.inl_injective⟩ := by
      ext z
      cases z <;> simp [L]
    have hQmap : Q = (Finset.univ.filter fun v => f' v = p).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
      ext z
      cases z <;> simp [Q]
    have hLsize : L.card = n / (Delta ^ 2) ∨ L.card = n / (Delta ^ 2) + 1 := by
      simpa only [hLmap, Finset.card_map] using hsizeσ p
    have hQsize : Q.card = n / (Delta ^ 2) ∨ Q.card = n / (Delta ^ 2) + 1 := by
      simpa only [hQmap, Finset.card_map] using hhostsize p
    have hdis : Disjoint L Q := by
      apply Finset.disjoint_left.mpr
      intro z hz hw
      obtain ⟨x, rfl, hx⟩ := (Finset.mem_filter.mp hz).2
      obtain ⟨v, hv, hvp⟩ := (Finset.mem_filter.mp hw).2
      exact Sum.inl_ne_inr hv
    obtain ⟨F, hFdec, hFC, hFsupport, hFreg⟩ :=
      hextractCand C L Q (n / (Delta ^ 2)) hnN hdis hLsize hQsize (hcandlow p)
    refine ⟨F, hFdec, hFC, ?_⟩
    simpa only [L, Q, B', σ, p, finProdFinEquiv.symm_apply_eq,
      finProdFinEquiv.apply_symm_apply,
      finProdFinEquiv.apply_eq_iff_eq_symm_apply] using hFreg
  obtain ⟨A', hA'A, hA'reg⟩ := TaggedCandidacyAssembly B A B' η c hcandextract
  refine ⟨G', hG'dec, B', A', hG'G, (fun _ => rfl), ?_, @hA'A, ?_, ?_, hA'reg⟩
  · intro v
    simpa only [B', finProdFinEquiv.symm_apply_apply] using hf' v
  · intro p
    change (Finset.univ.filter fun x => B₀.sourceCluster x = finProdFinEquiv p).card =
      (Finset.univ.filter fun v => finProdFinEquiv (f' v) = finProdFinEquiv p).card ∧ _
    simp only [hVeq, finProdFinEquiv.symm_apply_apply, hcapacity', hXeq]
    exact ⟨trivial, hsize p⟩
  · intro i j hij
    have hreg := hG'reg (finProdFinEquiv.symm i) (finProdFinEquiv.symm j) hij
    simpa only [B', hVeq] using hreg
