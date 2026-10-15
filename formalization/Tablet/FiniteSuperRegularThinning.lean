import Tablet.FiniteTripletRelabelling

universe u v

-- [TABLET NODE: FiniteSuperRegularThinning]
theorem FiniteSuperRegularThinning
    (N : ℕ) (eps p xi rho : ENNReal)
    (guarantee : ∀ {V : Type v} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V),
      Disjoint L R → N ≤ L.card → N ≤ R.card →
      L.card ≤ R.card + 1 → R.card ≤ L.card + 1 →
      SuperRegularPair G L R eps p →
      ∃ G' : SimpleGraph V, G' ≤ G ∧
        @SuperRegularPair V _ G' (Classical.decRel _) L R xi rho)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V)
    (hLR : Disjoint L R) (hL : N ≤ L.card) (hR : N ≤ R.card)
    (hnearL : L.card ≤ R.card + 1) (hnearR : R.card ≤ L.card + 1)
    (hG : SuperRegularPair G L R eps p) :
    ∃ G' : SimpleGraph V, G' ≤ G ∧
      @SuperRegularPair V _ G' (Classical.decRel _) L R xi rho := by
-- BODY
  classical
  let e : V ≃ ULift.{v} (Fin (Fintype.card V)) :=
    (Fintype.equivFin V).trans Equiv.ulift.symm
  let T := G.comap e.symm
  obtain ⟨_, _, hdisj, _, _, _, _, hsr, _, _⟩ :=
    FiniteTripletRelabelling e G L R hLR
  have card (S : Finset V) : (S.image e).card = S.card :=
    Finset.card_image_of_injective S e.injective
  obtain ⟨T', hsub, hT'⟩ := guarantee T (L.image e) (R.image e) hdisj
    (by simpa only [card] using hL) (by simpa only [card] using hR)
    (by simpa only [card] using hnearL) (by simpa only [card] using hnearR)
    ((hsr eps p).mp hG)
  let G' := T'.comap e
  letI : DecidableRel T'.Adj := Classical.decRel _
  refine ⟨G', ?_, ?_⟩
  · intro x y hxy
    have hh := hsub hxy
    simpa only [T, SimpleGraph.comap_adj, Equiv.symm_apply_apply] using hh
  · have hh := SuperRegularPairEmbedding e.symm e.symm.injective T' G'
      (L.image e) (R.image e) xi rho (fun x _ y _ => by simp [G']) hT'
    simpa only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
      Finset.image_id'] using hh
