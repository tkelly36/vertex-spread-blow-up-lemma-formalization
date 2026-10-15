import Tablet.ColourRoundInvariant

-- [TABLET NODE: ColourClassSequentialCompletion]
theorem ColourClassSequentialCompletion
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (epsilon density : ℕ → ENNReal)
    (D : ℕ) (C : ENNReal) (n round : ℕ)
    (step : ∀ (T : Finset (Fin r)) (Z : Finset VH)
      (ν : PMF (PartialCompatibleEmbedding B A Z)),
      (∀ j ∈ T, (colour j).val = round) →
      ColourRoundInvariant B A colour epsilon density D C n round T Z ν →
      ∀ i : Fin r, (colour i).val = round → i ∉ T →
        let Z' := Finset.univ.filter fun x : VH =>
          (colour (B.sourceCluster x)).val < round ∨
            B.sourceCluster x ∈ insert i T
        let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
        ∃ κ : PartialCompatibleEmbedding B A Z →
            PMF (PartialCompatibleEmbedding B A Z'),
          (∀ f ∈ ν.support, ∀ h ∈ (κ f).support, ∀ x ∈ Z,
            h.toFun x = f.toFun x) ∧
          (∀ f ∈ ν.support, VertexSpreadOn
            ((κ f).map fun h => fun y : {y : VH // y ∈ Y} => h.toFun y.1)
            (C / n) Set.univ) ∧
          ColourRoundInvariant B A colour epsilon density D C n round
            (insert i T) Z' (ν.bind κ))
    (S : Finset (Fin r)) (X : Finset VH)
    (μ : PMF (PartialCompatibleEmbedding B A X))
    (hS : ∀ j ∈ S, (colour j).val = round)
    (hμ : ColourRoundInvariant B A colour epsilon density D C n round S X μ) :
    let Bround := Finset.univ.filter fun j : Fin r => (colour j).val = round
    let Xfinal := Finset.univ.filter fun x : VH =>
      (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ Bround
    ∃ K : PartialCompatibleEmbedding B A X →
        PMF (PartialCompatibleEmbedding B A Xfinal),
      (∀ f ∈ μ.support, ∀ h ∈ (K f).support, ∀ x ∈ X,
        h.toFun x = f.toFun x) ∧
      ColourRoundInvariant B A colour epsilon density D C n round
        Bround Xfinal (μ.bind K) := by
-- BODY
  classical
  let Bround := Finset.univ.filter fun j : Fin r => (colour j).val = round
  let Xfinal := Finset.univ.filter fun x : VH =>
    (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ Bround
  change ∃ K : PartialCompatibleEmbedding B A X →
      PMF (PartialCompatibleEmbedding B A Xfinal),
    (∀ f ∈ μ.support, ∀ h ∈ (K f).support, ∀ x ∈ X,
      h.toFun x = f.toFun x) ∧
    ColourRoundInvariant B A colour epsilon density D C n round
      Bround Xfinal (μ.bind K)
  induction hcard : (Bround \ S).card using Nat.strong_induction_on
      generalizing S X μ with
  | h m ih =>
    have hSB : S ⊆ Bround := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hS j hj⟩
    by_cases hempty : Bround \ S = ∅
    · have hSfull : S = Bround :=
        Finset.Subset.antisymm hSB (Finset.sdiff_eq_empty_iff_subset.mp hempty)
      subst S
      have hX : X = Xfinal := hμ.2.2.2.2.1
      subst X
      refine ⟨PMF.pure, ?_, ?_⟩
      · intro f hf h hh x hx
        have heq : h = f := (PMF.mem_support_pure_iff _ _).mp hh
        subst h
        rfl
      · simpa only [PMF.bind_pure] using hμ
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hiB, hiS⟩ := Finset.mem_sdiff.mp hi
      have hicolour : (colour i).val = round := (Finset.mem_filter.mp hiB).2
      let Xnext := Finset.univ.filter fun x : VH =>
        (colour (B.sourceCluster x)).val < round ∨
          B.sourceCluster x ∈ insert i S
      obtain ⟨κ, hκagree, _, hκinv⟩ := step S X μ hS hμ i hicolour hiS
      have hnextS : ∀ j ∈ insert i S, (colour j).val = round := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hicolour
        · exact hS j hj
      have hdecrease : (Bround \ insert i S).card < m := by
        rw [← hcard]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro j hj
          obtain ⟨hjB, hjS⟩ := Finset.mem_sdiff.mp hj
          exact Finset.mem_sdiff.mpr
            ⟨hjB, fun h => hjS (Finset.mem_insert_of_mem h)⟩
        · intro heq
          have : i ∈ Bround \ insert i S := heq.symm ▸ hi
          exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self i S)
      obtain ⟨L, hLagree, hLinv⟩ :=
        ih (Bround \ insert i S).card hdecrease (insert i S) Xnext
          (μ.bind κ) hnextS hκinv rfl
      have hXXnext : X ⊆ Xnext := by
        intro x hx
        have hdomain := hμ.2.2.2.2.1
        rw [hdomain] at hx
        obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        exact hx.imp_right Finset.mem_insert_of_mem
      refine ⟨fun f => (κ f).bind L, ?_, ?_⟩
      · intro f hf h hh x hx
        obtain ⟨g, hg, hhg⟩ := (PMF.mem_support_bind_iff _ _ _).mp hh
        have hgμ : g ∈ (μ.bind κ).support :=
          (PMF.mem_support_bind_iff _ _ _).mpr ⟨f, hf, hg⟩
        exact (hLagree g hgμ h hhg x (hXXnext hx)).trans
          (hκagree f hf g hg x hx)
      · rw [← PMF.bind_bind]
        exact hLinv
