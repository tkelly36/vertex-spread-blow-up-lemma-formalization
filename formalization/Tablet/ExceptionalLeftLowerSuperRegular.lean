import Tablet.LowerSuperRegularPair
import Tablet.PairDensity

-- [TABLET NODE: ExceptionalLeftLowerSuperRegular]
theorem ExceptionalLeftLowerSuperRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
    (L₀ R₀ D_L D_R E : Finset V) (ε d ε' d' η : ENNReal)
    (hDL : D_L ⊆ L₀) (hDR : D_R ⊆ R₀)
    (hE : E ⊆ L₀ \ D_L)
    (hSR : LowerSuperRegularPair G₀ L₀ R₀ ε d)
    (hRows : ∀ x ∈ (L₀ \ D_L) \ E, ∀ y ∈ R₀ \ D_R,
      G.Adj x y ↔ G₀.Adj x y)
    (hEcard : (E.card : ENNReal) ≤ η * ((L₀ \ D_L).card : ENNReal))
    (hε'pos : 0 < ε') (hε'finite : ε' < ⊤)
    (hLeftThreshold : ε * (L₀.card : ENNReal) ≤
      ε' * ((L₀ \ D_L).card : ENNReal))
    (hRightThreshold : ε * (R₀.card : ENNReal) ≤
      ε' * ((R₀ \ D_R).card : ENNReal))
    (hDensityMargin : (d' - ε') + η / ε' ≤ d - ε)
    (hLeftDegree : (d' - ε') * ((R₀ \ D_R).card : ENNReal) ≤
      (d - ε) * (R₀.card : ENNReal) - (D_R.card : ENNReal))
    (hRightDegree : (d' - ε') * ((L₀ \ D_L).card : ENNReal) ≤
      (d - ε) * (L₀.card : ENNReal) - (D_L.card : ENNReal) -
        (E.card : ENNReal))
    (hExceptionalDegree : ∀ x ∈ E,
      (d' - ε') * ((R₀ \ D_R).card : ENNReal) ≤
        (((R₀ \ D_R).filter fun y => G.Adj x y).card : ENNReal)) :
    LowerSuperRegularPair G (L₀ \ D_L) (R₀ \ D_R) ε' d' := by
-- BODY
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S hS T hT hSsize hTsize
    have hS₀ : S ⊆ L₀ := hS.trans Finset.sdiff_subset
    have hT₀ : T ⊆ R₀ := hT.trans Finset.sdiff_subset
    have hOld := hSR.1 S hS₀ T hT₀
      (hLeftThreshold.trans_lt hSsize) (hRightThreshold.trans_lt hTsize)
    have hSpos : (S.card : ENNReal) ≠ 0 :=
      ne_of_gt (lt_of_le_of_lt (zero_le _) hSsize)
    have hTpos : (T.card : ENNReal) ≠ 0 :=
      ne_of_gt (lt_of_le_of_lt (zero_le _) hTsize)
    have hRectpos : (S.card : ENNReal) * (T.card : ENNReal) ≠ 0 :=
      mul_ne_zero hSpos hTpos
    have hRectfinite : (S.card : ENNReal) * (T.card : ENNReal) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) (by simp)
    have hCounts : ((S.product T).filter fun p => G₀.Adj p.1 p.2).card ≤
        ((S.product T).filter fun p => G.Adj p.1 p.2).card + E.card * T.card := by
      have hSubset : ((S.product T).filter fun p => G₀.Adj p.1 p.2) ⊆
          ((S.product T).filter fun p => G.Adj p.1 p.2) ∪ E.product T := by
        intro p hp
        obtain ⟨hpST, hpAdj⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hpST
        by_cases hpE : p.1 ∈ E
        · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hpE, hpT⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hpST, (hRows p.1 (Finset.mem_sdiff.mpr ⟨hS hpS, hpE⟩)
              p.2 (hT hpT)).mpr hpAdj⟩)
      have hUnion := Finset.card_union_le
        ((S.product T).filter fun p => G.Adj p.1 p.2) (E.product T)
      rw [Finset.product_eq_sprod (s := E) (t := T), Finset.card_product] at hUnion
      exact (Finset.card_le_card hSubset).trans hUnion
    have hCounts' :
        (((S.product T).filter fun p => G₀.Adj p.1 p.2).card : ENNReal) ≤
        (((S.product T).filter fun p => G.Adj p.1 p.2).card : ENNReal) +
          (E.card : ENNReal) * (T.card : ENNReal) := by
      exact_mod_cast hCounts
    have hLsize : ((L₀ \ D_L).card : ENNReal) ≤ (S.card : ENNReal) / ε' := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hε'pos))
        (Or.inl hε'finite.ne)).mpr
      simpa only [mul_comm] using hSsize.le
    have hEsize : (E.card : ENNReal) ≤ (η / ε') * (S.card : ENNReal) := by
      calc
        (E.card : ENNReal) ≤ η * ((L₀ \ D_L).card : ENNReal) := hEcard
        _ ≤ η * ((S.card : ENNReal) / ε') := mul_le_mul_right hLsize η
        _ = (η / ε') * (S.card : ENNReal) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    have hLoss : (E.card : ENNReal) * (T.card : ENNReal) ≤
        (η / ε') * ((S.card : ENNReal) * (T.card : ENNReal)) := by
      simpa only [mul_assoc] using mul_le_mul_left hEsize (T.card : ENNReal)
    have hOldCount : (d - ε) * ((S.card : ENNReal) * (T.card : ENNReal)) ≤
        (((S.product T).filter fun p => G₀.Adj p.1 p.2).card : ENNReal) := by
      exact (ENNReal.le_div_iff_mul_le (Or.inl hRectpos)
        (Or.inl hRectfinite)).mp hOld
    have hAdd :
        (d' - ε') * ((S.card : ENNReal) * (T.card : ENNReal)) +
          (E.card : ENNReal) * (T.card : ENNReal) ≤
        (((S.product T).filter fun p => G.Adj p.1 p.2).card : ENNReal) +
          (E.card : ENNReal) * (T.card : ENNReal) := by
      calc
        _ ≤ (d' - ε') * ((S.card : ENNReal) * (T.card : ENNReal)) +
            (η / ε') * ((S.card : ENNReal) * (T.card : ENNReal)) :=
          add_le_add_right hLoss _
        _ = ((d' - ε') + η / ε') *
            ((S.card : ENNReal) * (T.card : ENNReal)) := (add_mul _ _ _).symm
        _ ≤ (d - ε) * ((S.card : ENNReal) * (T.card : ENNReal)) :=
          mul_le_mul_left hDensityMargin _
        _ ≤ _ := hOldCount.trans hCounts'
    unfold PairDensity
    apply (ENNReal.le_div_iff_mul_le (Or.inl hRectpos)
      (Or.inl hRectfinite)).mpr
    exact (ENNReal.add_le_add_iff_right
      (ENNReal.mul_ne_top (by simp) (by simp))).mp hAdd
  · intro x hx
    by_cases hxE : x ∈ E
    · exact hExceptionalDegree x hxE
    · have hFilter : ((R₀ \ D_R).filter fun y => G.Adj x y) =
          (R₀.filter fun y => G₀.Adj x y) \ D_R := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨hyR, hyD⟩, hxy⟩
          exact ⟨⟨hyR, (hRows x (Finset.mem_sdiff.mpr ⟨hx, hxE⟩)
            y (Finset.mem_sdiff.mpr ⟨hyR, hyD⟩)).mp hxy⟩, hyD⟩
        · rintro ⟨⟨hyR, hxy⟩, hyD⟩
          exact ⟨⟨hyR, hyD⟩, (hRows x (Finset.mem_sdiff.mpr ⟨hx, hxE⟩)
            y (Finset.mem_sdiff.mpr ⟨hyR, hyD⟩)).mpr hxy⟩
      have hCard : (R₀.filter fun y => G₀.Adj x y).card ≤
          ((R₀ \ D_R).filter fun y => G.Adj x y).card + D_R.card := by
        rw [hFilter]
        exact Finset.card_le_card_sdiff_add_card
      have hCast : ((R₀.filter fun y => G₀.Adj x y).card : ENNReal) ≤
          (((R₀ \ D_R).filter fun y => G.Adj x y).card : ENNReal) +
            (D_R.card : ENNReal) := by
        exact_mod_cast hCard
      exact hLeftDegree.trans (tsub_le_iff_right.mpr
        ((hSR.2.1 x (Finset.mem_sdiff.mp hx).1).trans hCast))
  · intro y hy
    have hSubset : (((L₀.filter fun x => G₀.Adj x y) \ D_L) \ E) ⊆
        ((L₀ \ D_L).filter fun x => G.Adj x y) := by
      intro x hx
      obtain ⟨hxD, hxE⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨hx₀, hxDL⟩ := Finset.mem_sdiff.mp hxD
      obtain ⟨hxL, hxy⟩ := Finset.mem_filter.mp hx₀
      have hxResidual := Finset.mem_sdiff.mpr ⟨hxL, hxDL⟩
      exact Finset.mem_filter.mpr ⟨hxResidual,
        (hRows x (Finset.mem_sdiff.mpr ⟨hxResidual, hxE⟩) y hy).mpr hxy⟩
    have hCard : (L₀.filter fun x => G₀.Adj x y).card ≤
        ((L₀ \ D_L).filter fun x => G.Adj x y).card + D_L.card + E.card := by
      have h₁ : (L₀.filter fun x => G₀.Adj x y).card ≤
          ((L₀.filter fun x => G₀.Adj x y) \ D_L).card + D_L.card :=
        Finset.card_le_card_sdiff_add_card
      have h₂ : ((L₀.filter fun x => G₀.Adj x y) \ D_L).card ≤
          (((L₀.filter fun x => G₀.Adj x y) \ D_L) \ E).card + E.card :=
        Finset.card_le_card_sdiff_add_card
      have h₃ := Finset.card_le_card hSubset
      omega
    have hCast : ((L₀.filter fun x => G₀.Adj x y).card : ENNReal) ≤
        (((L₀ \ D_L).filter fun x => G.Adj x y).card : ENNReal) +
          (D_L.card : ENNReal) + (E.card : ENNReal) := by
      exact_mod_cast hCard
    apply hRightDegree.trans
    apply tsub_le_iff_right.mpr
    apply tsub_le_iff_right.mpr
    simpa only [add_assoc, add_comm, add_left_comm] using
      (hSR.2.2 y (Finset.mem_sdiff.mp hy).1).trans hCast
