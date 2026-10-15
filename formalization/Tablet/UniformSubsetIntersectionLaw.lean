import Tablet.HypergeometricMass

-- [TABLET NODE: UniformSubsetIntersectionLaw]
theorem UniformSubsetIntersectionLaw {V : Type*} [DecidableEq V]
    (S T : Finset V) (hTS : T ⊆ S) (s : ℕ) (hs : s ≤ S.card) (x : ℕ) :
    (((S.powersetCard s).filter fun U => (U ∩ T).card = x).card : ℝ) /
        ((S.powersetCard s).card : ℝ) =
      HypergeometricMass S.card s T.card x := by
-- BODY
  classical
  -- PMF.toOuterMeasure_uniformOfFinset_apply interprets this counting ratio as probability.
  by_cases hxs : x ≤ s
  · have hcount : ((S.powersetCard s).filter fun U => (U ∩ T).card = x).card =
        ((T.powersetCard x).product ((S \ T).powersetCard (s - x))).card := by
      apply Finset.card_bij (fun U _ => (U ∩ T, U \ T))
      · intro U hU
        obtain ⟨hUS, hUcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1
        have hUx := (Finset.mem_filter.mp hU).2
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hUx⟩,
          Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
        · intro v hv
          obtain ⟨hvU, hvT⟩ := Finset.mem_sdiff.mp hv
          exact Finset.mem_sdiff.mpr ⟨hUS hvU, hvT⟩
        · have hsum := Finset.card_sdiff_add_card_inter U T
          change (U \ T).card = s - x
          omega
      · intro U _ W _ hUW
        have hi : U ∩ T = W ∩ T := congrArg Prod.fst hUW
        have hd : U \ T = W \ T := congrArg Prod.snd hUW
        calc
          U = (U ∩ T) ∪ (U \ T) := by
            ext v
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            tauto
          _ = (W ∩ T) ∪ (W \ T) := by rw [hi, hd]
          _ = W := by
            ext v
            simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            tauto
      · intro P hP
        obtain ⟨hP1, hP2⟩ := Finset.mem_product.mp hP
        obtain ⟨hP1T, hP1card⟩ := Finset.mem_powersetCard.mp hP1
        obtain ⟨hP2ST, hP2card⟩ := Finset.mem_powersetCard.mp hP2
        have hP2T : Disjoint P.2 T := by
          apply Finset.disjoint_left.mpr
          intro v hvP hvT
          exact (Finset.mem_sdiff.mp (hP2ST hvP)).2 hvT
        have hdis : Disjoint P.1 P.2 :=
          (hP2T.symm).mono_left hP1T
        have hi : (P.1 ∪ P.2) ∩ T = P.1 := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hP1T,
            Finset.disjoint_iff_inter_eq_empty.mp hP2T, Finset.union_empty]
        have hd : (P.1 ∪ P.2) \ T = P.2 := by
          ext v
          constructor
          · intro hv
            obtain ⟨hvP, hvT⟩ := Finset.mem_sdiff.mp hv
            rcases Finset.mem_union.mp hvP with hv1 | hv2
            · exact (hvT (hP1T hv1)).elim
            · exact hv2
          · intro hv
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hv,
              (Finset.mem_sdiff.mp (hP2ST hv)).2⟩
        refine ⟨P.1 ∪ P.2, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨?_, ?_⟩, by simpa only [hi] using hP1card⟩, ?_⟩
        · exact Finset.union_subset (hP1T.trans hTS)
            (hP2ST.trans Finset.sdiff_subset)
        · rw [Finset.card_union_of_disjoint hdis, hP1card, hP2card]
          omega
        · exact Prod.ext hi hd
    rw [hcount]
    have hprod := Finset.card_product (T.powersetCard x) ((S \ T).powersetCard (s - x))
    change (Finset.product (T.powersetCard x) ((S \ T).powersetCard (s - x))).card =
      (T.powersetCard x).card * ((S \ T).powersetCard (s - x)).card at hprod
    rw [hprod]
    simp only [Finset.card_powersetCard,
      Finset.card_sdiff_of_subset hTS, Nat.cast_mul, HypergeometricMass, if_pos hxs]
  · have hzero : ((S.powersetCard s).filter fun U => (U ∩ T).card = x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      have hcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
      have hx := (Finset.mem_filter.mp hU).2
      have hle := Finset.card_le_card (Finset.inter_subset_left : U ∩ T ⊆ U)
      omega
    simp only [hzero, Finset.card_empty, Nat.cast_zero, zero_div,
      HypergeometricMass, if_neg hxs]
