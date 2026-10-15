import Tablet.SuperRegularPair

-- [TABLET NODE: FutureExtraVertexStability]
theorem FutureExtraVertexStability :
    ∀ (m k : ℕ) (ε ε' d : ENNReal),
      1 ≤ m → ε < ε' → ε' ≤ 1 → d ≤ 1 →
      ε + (2 : ENNReal) / (m : ENNReal) ≤ ε' →
      ε + 1 / (ε' * (m : ENNReal)) ≤ ε' →
      ∀ {V : Type*} [DecidableEq V]
        (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
        (L R : Finset V) (x : V),
        Disjoint L R → x ∉ L → x ∉ R → L.card = m →
        (R.card = m ∨ R.card = m + 1) →
        G ≤ T → k ≤ (R.filter fun y => T.Adj x y).card →
        (d - ε') * (R.card : ENNReal) ≤ k →
        (k : ENNReal) ≤ (d + ε') * (R.card : ENNReal) →
        SuperRegularPair G L R ε d →
        ∃ (N : Finset V) (G' : SimpleGraph V),
          N ⊆ R ∧ N.card = k ∧ N ⊆ (R.filter fun y => T.Adj x y) ∧ G' ≤ T ∧
          (∀ y ∈ R, G'.Adj x y ↔ y ∈ N) ∧
          (∀ u v, u ≠ x → v ≠ x → (G'.Adj u v ↔ G.Adj u v)) ∧
          @SuperRegularPair V _ G' (Classical.decRel _) (insert x L) R ε' d := by
-- BODY
  intro m k ε ε' d hm hε hε' hd hslack hslackReg V _ G T _ _ L R x
    _ hxL hxR hL _ hGT hk hkLower hkUpper hsuper
  classical
  obtain ⟨N, hN, hNk⟩ := Finset.exists_subset_card_eq hk
  have hNR : N ⊆ R := hN.trans (Finset.filter_subset _ _)
  have hxN : x ∉ N := fun h => hxR (hNR h)
  let G' : SimpleGraph V := {
    Adj := fun u v => (u ≠ x ∧ v ≠ x ∧ G.Adj u v) ∨
      (u = x ∧ v ∈ N) ∨ (v = x ∧ u ∈ N)
    symm := by
      intro u v h
      rcases h with ⟨hu, hv, huv⟩ | ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact Or.inl ⟨hv, hu, G.symm huv⟩
      · exact Or.inr (Or.inr ⟨hu, hv⟩)
      · exact Or.inr (Or.inl ⟨hv, hu⟩)
    loopless := by
      refine ⟨?_⟩
      intro u h
      rcases h with ⟨_, _, huu⟩ | ⟨rfl, hu⟩ | ⟨rfl, hu⟩
      · exact G.loopless.irrefl u huu
      · exact hxN hu
      · exact hxN hu }
  letI : DecidableRel G'.Adj := Classical.decRel _
  have haway : ∀ u v, u ≠ x → v ≠ x → (G'.Adj u v ↔ G.Adj u v) := by
    intro u v hu hv
    change ((u ≠ x ∧ v ≠ x ∧ G.Adj u v) ∨
      (u = x ∧ v ∈ N) ∨ (v = x ∧ u ∈ N)) ↔ _
    exact ⟨fun h => by
      rcases h with ⟨_, _, huv⟩ | ⟨hux, _⟩ | ⟨hvx, _⟩
      · exact huv
      · exact (hu hux).elim
      · exact (hv hvx).elim, fun h => Or.inl ⟨hu, hv, h⟩⟩
  have hrow : ∀ y, G'.Adj x y ↔ y ∈ N := by
    intro y
    change ((x ≠ x ∧ y ≠ x ∧ G.Adj x y) ∨
      (x = x ∧ y ∈ N) ∨ (y = x ∧ x ∈ N)) ↔ _
    simp only [ne_self_iff_false, false_and, false_or, true_and, hxN, and_false,
      or_false]
  have hsub : G' ≤ T := by
    intro u v h
    rcases h with ⟨_, _, huv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · exact hGT huv
    · exact (Finset.mem_filter.mp (hN hv)).2
    · exact T.symm (Finset.mem_filter.mp (hN hu)).2
  refine ⟨N, G', hNR, hNk, hN, hsub, (fun y _ => hrow y), haway, ?_⟩
  have hεle : ε ≤ ε' := hε.le
  have hεone : ε ≤ 1 := hεle.trans hε'
  have hm0 : (m : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
  have hmt : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hbudget : ε * m + 2 ≤ ε' * m := by
    have h := mul_le_mul_left hslack (m : ENNReal)
    rwa [add_mul, ENNReal.div_mul_cancel hm0 hmt] at h
  have hsize : ((insert x L).card : ENNReal) = (m : ENNReal) + 1 := by
    simp only [Finset.card_insert_of_notMem hxL, hL, Nat.cast_add, Nat.cast_one]
  have hLcast : (L.card : ENNReal) = m := by rw [hL]
  have hleftEq : ∀ v ∈ L, (R.filter fun w => G'.Adj v w) =
      (R.filter fun w => G.Adj v w) := by
    intro v hv
    apply Finset.filter_congr
    intro w hw
    exact haway v w (fun h => hxL (h ▸ hv)) (fun h => hxR (h ▸ hw))
  have hrightEq : ∀ w ∈ R, (L.filter fun v => G'.Adj v w) =
      (L.filter fun v => G.Adj v w) := by
    intro w hw
    apply Finset.filter_congr
    intro v hv
    exact haway v w (fun h => hxL (h ▸ hv)) (fun h => hxR (h ▸ hw))
  rcases hsuper with ⟨hreg, hleft, hright⟩
  refine ⟨?_, ?_, ?_⟩
  · have hagree : ∀ U ⊆ L, ∀ W ⊆ R,
        ((U.product W).filter fun p : V × V => G'.Adj p.1 p.2) =
        ((U.product W).filter fun p : V × V => G.Adj p.1 p.2) := by
      intro U hU W hW
      apply Finset.filter_congr
      intro p hp
      obtain ⟨hu, hw⟩ := Finset.mem_product.mp hp
      exact haway p.1 p.2 (fun h => hxL (h ▸ hU hu))
        (fun h => hxR (h ▸ hW hw))
    have hdensityEq : ∀ U ⊆ L, ∀ W ⊆ R, PairDensity G' U W = PairDensity G U W := by
      intro U hU W hW
      unfold PairDensity
      rw [hagree U hU W hW]
    intro U hU W hW hUsize hWsize
    have hWold : ε * (R.card : ENNReal) < W.card :=
      (mul_le_mul_left hεle _).trans_lt hWsize
    have hthreshold : ε * m ≤ ε' * ((m : ENNReal) + 1) :=
      (mul_le_mul_left hεle _).trans (mul_le_mul_right (le_add_right le_rfl) ε')
    by_cases hxU : x ∈ U
    · let U0 := U.erase x
      have hU0L : U0 ⊆ L := by
        intro u hu
        obtain ⟨hux, hu⟩ := Finset.mem_erase.mp hu
        exact (Finset.mem_insert.mp (hU hu)).resolve_left hux
      have hUcard : (U.card : ENNReal) = (U0.card : ENNReal) + 1 := by
        exact_mod_cast (Finset.card_erase_add_one hxU).symm
      have hUold : ε * (L.card : ENNReal) < U0.card := by
        rw [hLcast]
        apply (ENNReal.add_lt_add_iff_right ENNReal.one_ne_top).mp
        calc
          ε * (m : ENNReal) + 1 ≤ ε * m + 2 := add_le_add le_rfl (by norm_num)
          _ ≤ ε' * m := hbudget
          _ ≤ ε' * ((m : ENNReal) + 1) :=
            mul_le_mul_right (le_add_right le_rfl) ε'
          _ < (U.card : ENNReal) := by simpa only [hsize] using hUsize
          _ = (U0.card : ENNReal) + 1 := hUcard
      obtain ⟨hlower, hupper⟩ := hreg U0 hU0L W hW hUold hWold
      have hu00 : (U0.card : ENNReal) ≠ 0 :=
        ne_of_gt (bot_le.trans_lt hUold)
      have hu0t : (U0.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hu0 : (U.card : ENNReal) ≠ 0 :=
        ne_of_gt (bot_le.trans_lt hUsize)
      have hut : (U.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hw0 : (W.card : ENNReal) ≠ 0 :=
        ne_of_gt (bot_le.trans_lt hWold)
      have hwt : (W.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      let a : ENNReal := ((U.product W).filter fun p : V × V => G'.Adj p.1 p.2).card
      let b : ENNReal := ((U0.product W).filter fun p : V × V => G.Adj p.1 p.2).card
      let p := PairDensity G' U W
      let q := PairDensity G U0 W
      have hcountLower : b ≤ a := by
        dsimp only [a, b]
        erw [← hagree U0 hU0L W hW]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.product_subset_product (Finset.erase_subset x U) (Finset.Subset.refl W)))
      have hcountUpper : a ≤ b + (W.card : ENNReal) := by
        have hdecomp : U = U0 ∪ {x} := by
          ext u
          by_cases hux : u = x
          · subst u
            simp [hxU]
          · simp [U0, hux]
        have hnat : ((U.product W).filter fun p : V × V => G'.Adj p.1 p.2).card ≤
            ((U0.product W).filter fun p : V × V => G.Adj p.1 p.2).card + W.card := by
          rw [hdecomp]
          simp only [Finset.product_eq_sprod, Finset.union_product, Finset.filter_union]
          erw [hagree U0 hU0L W hW]
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
            ((Finset.card_filter_le _ _).trans (by
              simp only [Finset.card_product, Finset.card_singleton, one_mul]
              exact le_rfl)) _)
        dsimp only [a, b]
        exact_mod_cast hnat
      have hqone : q ≤ 1 := by
        change b / ((U0.card : ENNReal) * (W.card : ENNReal)) ≤ 1
        apply (ENNReal.div_le_iff (mul_ne_zero hu00 hw0)
          (ENNReal.mul_ne_top hu0t hwt)).mpr
        rw [one_mul]
        dsimp [b]
        exact_mod_cast (Finset.card_filter_le (U0.product W) _).trans_eq
          (Finset.card_product U0 W)
      have hpMul : p * (U.card : ENNReal) = a / (W.card : ENNReal) := by
        change (a / ((U.card : ENNReal) * (W.card : ENNReal))) * (U.card : ENNReal) = _
        rw [← ENNReal.mul_div_right_comm, mul_comm a,
          ENNReal.mul_div_mul_left _ _ hu0 hut]
      have hqMul : q * (U0.card : ENNReal) = b / (W.card : ENNReal) := by
        change (b / ((U0.card : ENNReal) * (W.card : ENNReal))) * (U0.card : ENNReal) = _
        rw [← ENNReal.mul_div_right_comm, mul_comm b,
          ENNReal.mul_div_mul_left _ _ hu00 hu0t]
      have hpq : p ≤ q + 1 / (U.card : ENNReal) := by
        apply (ENNReal.mul_le_mul_iff_left hu0 hut).mp
        rw [add_mul, ENNReal.div_mul_cancel hu0 hut, hpMul]
        calc
          a / (W.card : ENNReal) ≤ (b + (W.card : ENNReal)) / W.card :=
            ENNReal.div_le_div_right hcountUpper _
          _ = b / (W.card : ENNReal) + 1 := by
            rw [ENNReal.add_div, ENNReal.div_self hw0 hwt]
          _ = q * (U0.card : ENNReal) + 1 := by rw [hqMul]
          _ ≤ q * (U.card : ENNReal) + 1 := add_le_add
            (mul_le_mul_right (by exact_mod_cast Finset.card_le_card (Finset.erase_subset x U)) q)
            le_rfl
      have hqp : q ≤ p + 1 / (U.card : ENNReal) := by
        apply (ENNReal.mul_le_mul_iff_left hu0 hut).mp
        rw [add_mul, ENNReal.div_mul_cancel hu0 hut, hpMul, hUcard,
          mul_add, mul_one, hqMul]
        exact add_le_add (ENNReal.div_le_div_right hcountLower _) hqone
      have hdelta : 1 / (U.card : ENNReal) ≤ 1 / (ε' * (m : ENNReal)) := by
        apply ENNReal.div_le_div_left
        exact (mul_le_mul_right (le_add_right le_rfl) ε').trans
          (by simpa only [hsize] using hUsize.le)
      have herror : ε + 1 / (U.card : ENNReal) ≤ ε' :=
        (add_le_add le_rfl hdelta).trans hslackReg
      constructor
      · change d - ε' ≤ p
        apply tsub_le_iff_right.mpr
        have hdq : d ≤ q + ε := tsub_le_iff_right.mp hlower
        calc
          d ≤ q + ε := hdq
          _ ≤ (p + 1 / (U.card : ENNReal)) + ε := add_le_add hqp le_rfl
          _ = p + (ε + 1 / (U.card : ENNReal)) := by rw [add_assoc, add_comm _ ε]
          _ ≤ p + ε' := add_le_add le_rfl herror
      · change p ≤ d + ε'
        calc
          p ≤ q + 1 / (U.card : ENNReal) := hpq
          _ ≤ (d + ε) + 1 / (U.card : ENNReal) := add_le_add hupper le_rfl
          _ = d + (ε + 1 / (U.card : ENNReal)) := add_assoc _ _ _
          _ ≤ d + ε' := add_le_add le_rfl herror
    · have hUL : U ⊆ L := by
        intro u hu
        exact (Finset.mem_insert.mp (hU hu)).resolve_left (fun h => hxU (h ▸ hu))
      have hUold : ε * (L.card : ENNReal) < U.card := by
        rw [hLcast]
        exact hthreshold.trans_lt (by simpa only [hsize] using hUsize)
      obtain ⟨hlower, hupper⟩ := hreg U hUL W hW hUold hWold
      rw [hdensityEq U hUL W hW]
      exact ⟨(tsub_le_tsub_left hεle d).trans hlower,
        hupper.trans (add_le_add le_rfl hεle)⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with hvx | hv
    · subst v
      have hfilter : (R.filter fun w => G'.Adj x w) = N := by
        ext w
        simp only [Finset.mem_filter, hrow]
        exact ⟨And.right, fun hw => ⟨hNR hw, hw⟩⟩
      rw [hfilter, hNk]
      exact ⟨hkLower, hkUpper⟩
    · rw [hleftEq v hv]
      obtain ⟨hlower, hupper⟩ := hleft v hv
      exact ⟨(mul_le_mul_left (tsub_le_tsub_left hεle d) _).trans hlower,
        hupper.trans (mul_le_mul_left (add_le_add le_rfl hεle) _)⟩
  · intro w hw
    obtain ⟨hlower, hupper⟩ := hright w hw
    rw [hLcast] at hupper
    have hcountLower : ((L.filter fun v => G.Adj v w).card : ENNReal) ≤
        (((insert x L).filter fun v => G'.Adj v w).card : ENNReal) := by
      rw [← hrightEq w hw]
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_insert x L))
    have hcountUpper : (((insert x L).filter fun v => G'.Adj v w).card : ENNReal) ≤
        ((L.filter fun v => G.Adj v w).card : ENNReal) + 1 := by
      have hnat : ((insert x L).filter fun v => G'.Adj v w).card ≤
          (L.filter fun v => G.Adj v w).card + 1 := by
        rw [Finset.filter_insert, hrightEq w hw]
        split_ifs
        · exact Finset.card_insert_le _ _
        · exact Nat.le_add_right _ _
      exact_mod_cast hnat
    constructor
    · rw [hsize, ENNReal.sub_mul (fun _ _ => ENNReal.add_ne_top.mpr
        ⟨hmt, ENNReal.one_ne_top⟩), tsub_le_iff_right]
      rw [hLcast, ENNReal.sub_mul (fun _ _ => hmt), tsub_le_iff_right] at hlower
      have herror : ε * m + d ≤ ε' * ((m : ENNReal) + 1) := by
        calc
          ε * m + d ≤ ε * m + 2 := add_le_add le_rfl (hd.trans (by norm_num))
          _ ≤ ε' * m := hbudget
          _ ≤ ε' * ((m : ENNReal) + 1) :=
            mul_le_mul_right (le_add_right le_rfl) ε'
      calc
        d * ((m : ENNReal) + 1) = d * m + d := by rw [mul_add, mul_one]
        _ ≤ ((L.filter fun v => G.Adj v w).card : ENNReal) + ε * m + d :=
          add_le_add hlower le_rfl
        _ = ((L.filter fun v => G.Adj v w).card : ENNReal) + (ε * m + d) :=
          add_assoc _ _ _
        _ ≤ (((insert x L).filter fun v => G'.Adj v w).card : ENNReal) +
            ε' * ((m : ENNReal) + 1) := add_le_add hcountLower herror
    · rw [hsize]
      calc
        (((insert x L).filter fun v => G'.Adj v w).card : ENNReal) ≤
            ((L.filter fun v => G.Adj v w).card : ENNReal) + 1 := hcountUpper
        _ ≤ (d + ε) * m + 1 := add_le_add hupper le_rfl
        _ = d * m + (ε * m + 1) := by rw [add_mul, add_assoc]
        _ ≤ d * m + (ε * m + 2) := add_le_add le_rfl (add_le_add le_rfl (by norm_num))
        _ ≤ d * m + ε' * m := add_le_add le_rfl hbudget
        _ = (d + ε') * m := (add_mul _ _ _).symm
        _ ≤ (d + ε') * ((m : ENNReal) + 1) :=
          mul_le_mul_right (le_add_right le_rfl) _
