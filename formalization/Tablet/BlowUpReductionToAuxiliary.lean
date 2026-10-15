import Tablet.EquitableSquareColoring
import Tablet.MatchingCompletionExtension
import Tablet.SimultaneousHostCandidacyRefinement
import Tablet.RegularSubgraph
import Tablet.SuperRegularSubgraph

-- [TABLET NODE: BlowUpReductionToAuxiliary]
theorem BlowUpReductionToAuxiliary :
    ∀ (Delta : ℕ) (ε' d' d : ENNReal), 1 ≤ Delta → 0 < ε' → ε' < 1 →
      0 < d' → d' < d ^ 2 / 2 → d ≤ 1 →
      ∃ ε : ENNReal, 0 < ε ∧ ε < ε' ∧
      ∀ r : ℕ, ∃ n₀ : ℕ,
      ∀ (n : ℕ), n₀ ≤ n →
      ∀ {VH VG : Type*} [Fintype VH] [Fintype VG]
        [DecidableEq VH] [DecidableEq VG]
        {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
        [DecidableRel H.Adj] [DecidableRel G.Adj] [DecidableRel R.Adj]
        (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B),
        (∀ i,
          (Finset.univ.filter fun x : VH => B.sourceCluster x = i).card = n ∧
          (Finset.univ.filter fun v : VG => B.hostCluster v = i).card = n) →
        H.maxDegree ≤ Delta → R.maxDegree ≤ Delta →
        InstanceLowerSuperRegular B ε d → CandidacyLowerSuperRegular B A ε d →
        ∃ (H' : SimpleGraph VH) (G' : SimpleGraph VG)
          (R' : SimpleGraph (Fin r × Fin (Delta ^ 2)))
          (_ : DecidableRel H'.Adj) (_ : DecidableRel G'.Adj) (_ : DecidableRel R'.Adj)
          (B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G'
            (R'.comap finProdFinEquiv.symm)) (A' : CandidacySystem B'),
          H ≤ H' ∧ G' ≤ G ∧
          (∀ {x v}, A'.allowed x v → A.allowed x v) ∧
          (∀ x, (finProdFinEquiv.symm (B'.sourceCluster x)).1 = B.sourceCluster x) ∧
          (∀ v, (finProdFinEquiv.symm (B'.hostCluster v)).1 = B.hostCluster v) ∧
          (∀ p,
            let X := Finset.univ.filter fun x : VH => B'.sourceCluster x = finProdFinEquiv p
            let V := Finset.univ.filter fun v : VG => B'.hostCluster v = finProdFinEquiv p
            X.card = V.card ∧
              (X.card = n / (Delta ^ 2) ∨ X.card = n / (Delta ^ 2) + 1)) ∧
          (∀ p q, R'.Adj p q ↔ R.Adj p.1 q.1) ∧
          H'.maxDegree ≤ Delta ^ 3 ∧ R'.maxDegree ≤ Delta ^ 3 ∧
          InstanceSuperRegular B' ε' d' ∧ CandidacySuperRegular B' A' ε' d' ∧
          ∀ p q, R'.Adj p q →
            SaturatingSourcePair B' (finProdFinEquiv p) (finProdFinEquiv q) := by
-- BODY
  classical
  intro Delta ε' d' d hDelta hε' hε'one hd' hd'd hdone
  obtain ⟨ε, hε, hεlt, hrefine⟩ := SimultaneousHostCandidacyRefinement
    Delta ε' d' d hDelta hε' hε'one hd' hd'd hdone
  refine ⟨ε, hε, hεlt, ?_⟩
  intro r
  obtain ⟨n₀, hn₀⟩ := hrefine r
  refine ⟨n₀, ?_⟩
  intro n hn VH VG _ _ _ _ H G R _ _ _ B A hsizes hH hR hB hA
  obtain ⟨color, hcolorSizes, hcolorIndependent⟩ :=
    EquitableSquareColoring Delta r n hDelta B hH (fun i => (hsizes i).1)
  obtain ⟨H', R', instH', instR', B₀, hHH', hsource₀, hsupport, hdegreeR, hsat₀⟩ :=
    MatchingCompletionExtension Delta r n hDelta B color
      hcolorSizes hcolorIndependent hR
  letI := instH'
  letI := instR'
  have hprojection₀ (x : VH) :
      (finProdFinEquiv.symm (B₀.sourceCluster x)).1 = B.sourceCluster x :=
    congrArg Prod.fst (hsource₀ x)
  have hfiber₀ (p : Fin r × Fin (Delta ^ 2)) :
      (Finset.univ.filter fun x : VH =>
        B₀.sourceCluster x = finProdFinEquiv p).card = n / (Delta ^ 2) ∨
      (Finset.univ.filter fun x : VH =>
        B₀.sourceCluster x = finProdFinEquiv p).card = n / (Delta ^ 2) + 1 := by
    have heq (x : VH) : B₀.sourceCluster x = finProdFinEquiv p ↔
        B.sourceCluster x = p.1 ∧ color x = p.2 := by
      rw [← finProdFinEquiv.symm_apply_eq, hsource₀ x]
      exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
        fun h => Prod.ext h.1 h.2⟩
    simpa only [heq] using hcolorSizes p.1 p.2
  have hunique (x y z : VH) (hxy : H'.Adj x y) (hxz : H'.Adj x z)
      (hyz : B₀.sourceCluster y = B₀.sourceCluster z) : y = z := by
    let p := finProdFinEquiv.symm (B₀.sourceCluster x)
    let q := finProdFinEquiv.symm (B₀.sourceCluster y)
    have hp : B₀.sourceCluster x = finProdFinEquiv p :=
      (finProdFinEquiv.apply_symm_apply _).symm
    have hq : B₀.sourceCluster y = finProdFinEquiv q :=
      (finProdFinEquiv.apply_symm_apply _).symm
    have hz : B₀.sourceCluster z = finProdFinEquiv q := hyz.symm.trans hq
    have hadj : R'.Adj p q := B₀.reduced_support hxy
    let x₀ : {x : VH // B₀.sourceCluster x = finProdFinEquiv p} := ⟨x, hp⟩
    let y₀ : {y : VH // B₀.sourceCluster y = finProdFinEquiv q} := ⟨y, hq⟩
    let z₀ : {y : VH // B₀.sourceCluster y = finProdFinEquiv q} := ⟨z, hz⟩
    rcases hsat₀ p q hadj with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
    · have hy : y₀ = τ x₀ := (hτ x₀ y₀).mp hxy
      have hz : z₀ = τ x₀ := (hτ x₀ z₀).mp hxz
      exact congrArg Subtype.val (hy.trans hz.symm)
    · have hy : x₀ = τ y₀ := (hτ x₀ y₀).mp hxy
      have hz : x₀ = τ z₀ := (hτ x₀ z₀).mp hxz
      exact congrArg Subtype.val (τ.injective (hy.symm.trans hz))
  have hdegreeH : H'.maxDegree ≤ Delta ^ 3 := by
    apply H'.maxDegree_le_of_forall_degree_le
    intro x
    let p := finProdFinEquiv.symm (B₀.sourceCluster x)
    let f : H'.neighborSet x → R'.neighborSet p := fun y =>
      ⟨finProdFinEquiv.symm (B₀.sourceCluster y.1), B₀.reduced_support y.2⟩
    have hf : Function.Injective f := by
      intro y z heq
      apply Subtype.ext
      apply hunique x y.1 z.1 y.2 z.2
      exact finProdFinEquiv.symm.injective (congrArg Subtype.val heq)
    calc
      H'.degree x = Fintype.card (H'.neighborSet x) :=
        (SimpleGraph.card_neighborSet_eq_degree H' x).symm
      _ ≤ Fintype.card (R'.neighborSet p) := Fintype.card_le_of_injective f hf
      _ = R'.degree p := SimpleGraph.card_neighborSet_eq_degree R' p
      _ ≤ R'.maxDegree := R'.degree_le_maxDegree p
      _ ≤ Delta ^ 3 := hdegreeR
  obtain ⟨G', instG', B', A', hG', hsource, hhost, hallowed, hfibers, hsuper, hcan⟩ :=
    hn₀ n hn B A B₀ hsizes hHH' hprojection₀
      (fun p q hpq => (hsupport p q).mp hpq) hfiber₀ hB hA
  letI := instG'
  refine ⟨H', G', R', instH', instG', instR', B', A', hHH', hG',
    hallowed, ?_, hhost, hfibers, hsupport, hdegreeH, hdegreeR, hsuper, hcan, ?_⟩
  · intro x
    rw [hsource x]
    exact hprojection₀ x
  · intro p q hpq
    have hmap : B'.sourceCluster = B₀.sourceCluster := funext hsource
    unfold SaturatingSourcePair
    rw [hmap]
    exact hsat₀ p q hpq
