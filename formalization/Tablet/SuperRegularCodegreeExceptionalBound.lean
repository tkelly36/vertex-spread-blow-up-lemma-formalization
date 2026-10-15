import Tablet.SuperRegularPair
import Tablet.FilteredProductRowCount

-- [TABLET NODE: SuperRegularCodegreeExceptionalBound]
theorem SuperRegularCodegreeExceptionalBound :
    ∀ {V : Type*} [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (n : ℕ) (ε d : ENNReal),
      U.card = n → n ≠ 0 → 2 * ε < d →
      SuperRegularPair G U W ε d →
      (((W ×ˢ W).filter fun z =>
          let C := (U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card
          (C : ENNReal) < (d - 2 * ε) ^ 2 * n ∨
            (d + 2 * ε) ^ 2 * n < (C : ENNReal)).card : ENNReal) ≤
        2 * ε * (W.card : ENNReal) ^ 2 := by
-- BODY
  classical
  intro V _ G _ U W n ε d hU hn hε hsr
  have hnzero : (n : ENNReal) ≠ 0 := by exact_mod_cast hn
  have hεsub : ε < d - ε := by
    by_contra h
    have hd := tsub_le_iff_right.mp (le_of_not_gt h)
    rw [← two_mul] at hd
    exact (not_le_of_gt hε) hd
  have hεtwo : ε ≤ 2 * ε := by
    simpa only [one_mul] using (mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2) ε)
  have hsub : d - 2 * ε ≤ d - ε := tsub_le_tsub_left hεtwo d
  have hadd : d + ε ≤ d + 2 * ε := add_le_add_right hεtwo d
  have hrow : ∀ w ∈ W,
      ((W.filter fun w' =>
        ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal) <
            (d - 2 * ε) ^ 2 * n ∨
          (d + 2 * ε) ^ 2 * n <
            ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal)).card : ENNReal)
        ≤ 2 * ε * W.card := by
    intro w hw
    let A := U.filter fun u => G.Adj u w
    have hdeg := hsr.2.2 w hw
    have hAlower : (d - ε) * n ≤ (A.card : ENNReal) := by
      simpa only [hU] using hdeg.1
    have hAupper : (A.card : ENNReal) ≤ (d + ε) * n := by
      simpa only [hU] using hdeg.2
    have hAsize : ε * U.card < (A.card : ENNReal) := by
      rw [hU]
      exact (ENNReal.mul_lt_mul_left hnzero (by simp) hεsub).trans_le hAlower
    have hAzero : (A.card : ENNReal) ≠ 0 :=
      ne_of_gt ((zero_le _).trans_lt hAsize)
    have hcommon : ∀ w', A.filter (fun u => G.Adj u w') =
        U.filter (fun u => G.Adj u w ∧ G.Adj u w') := by
      intro w'
      ext u
      simp only [A, Finset.mem_filter, and_assoc]
    have hcount : ∀ T : Finset V,
        (((A.product T).filter fun p => G.Adj p.1 p.2).card : ENNReal) =
          ∑ w' ∈ T, ((A.filter fun u => G.Adj u w').card : ENNReal) := by
      intro T
      have hn : ((A.product T).filter fun p => G.Adj p.1 p.2).card =
          ∑ w' ∈ T, (A.filter fun u => G.Adj u w').card := by
        rw [FilteredProductRowCount A T G.Adj]
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        exact Finset.sum_comm (f := fun u w' => if G.Adj u w' then (1 : ℕ) else 0)
      rw [hn, Nat.cast_sum]
    have hlo : (d - 2 * ε) ^ 2 * n ≤ (d - ε) * A.card := by
      calc
        (d - 2 * ε) ^ 2 * n ≤ (d - ε) ^ 2 * n := by gcongr
        _ = (d - ε) * ((d - ε) * n) := by rw [pow_two, mul_assoc]
        _ ≤ (d - ε) * A.card := mul_le_mul_left' hAlower _
    have hhi : (d + ε) * A.card ≤ (d + 2 * ε) ^ 2 * n := by
      calc
        (d + ε) * A.card ≤ (d + ε) * ((d + ε) * n) := mul_le_mul_left' hAupper _
        _ = (d + ε) ^ 2 * n := by rw [pow_two, mul_assoc]
        _ ≤ (d + 2 * ε) ^ 2 * n := by gcongr
    let L := W.filter fun w' =>
      ((A.filter fun u => G.Adj u w').card : ENNReal) < (d - 2 * ε) ^ 2 * n
    let H := W.filter fun w' =>
      (d + 2 * ε) ^ 2 * n < ((A.filter fun u => G.Adj u w').card : ENNReal)
    have hL : (L.card : ENNReal) ≤ ε * W.card := by
      by_contra hbound
      have hsize : ε * W.card < (L.card : ENNReal) := lt_of_not_ge hbound
      have hzero : (L.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hsize)
      have hnonempty : L.Nonempty := Finset.card_pos.mp (by exact_mod_cast
        ((zero_le _).trans_lt hsize : (0 : ENNReal) < L.card))
      have hsum : (∑ w' ∈ L, ((A.filter fun u => G.Adj u w').card : ENNReal)) <
          ∑ _w' ∈ L, (d - ε) * A.card := by
        apply ENNReal.sum_lt_sum_of_nonempty hnonempty
        intro w' hw'
        exact (Finset.mem_filter.mp hw').2 |>.trans_le hlo
      have hdensity : PairDensity G A L < d - ε := by
        unfold PairDensity
        apply (ENNReal.div_lt_iff (Or.inl (mul_ne_zero hAzero hzero))
          (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))).mpr
        rw [hcount]
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm,
          mul_left_comm] using hsum
      exact (not_lt_of_ge (hsr.1 A (Finset.filter_subset _ _) L
        (Finset.filter_subset _ _) hAsize hsize).1) hdensity
    have hH : (H.card : ENNReal) ≤ ε * W.card := by
      by_contra hbound
      have hsize : ε * W.card < (H.card : ENNReal) := lt_of_not_ge hbound
      have hzero : (H.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hsize)
      have hnonempty : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast
        ((zero_le _).trans_lt hsize : (0 : ENNReal) < H.card))
      have hsum : (∑ _w' ∈ H, (d + ε) * A.card) <
          ∑ w' ∈ H, ((A.filter fun u => G.Adj u w').card : ENNReal) := by
        apply ENNReal.sum_lt_sum_of_nonempty hnonempty
        intro w' hw'
        exact hhi.trans_lt (Finset.mem_filter.mp hw').2
      have hdensity : d + ε < PairDensity G A H := by
        unfold PairDensity
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl (mul_ne_zero hAzero hzero))
          (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))).mpr
        rw [hcount]
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm,
          mul_left_comm] using hsum
      exact (not_lt_of_ge (hsr.1 A (Finset.filter_subset _ _) H
        (Finset.filter_subset _ _) hAsize hsize).2) hdensity
    have hunion : (W.filter fun w' =>
        ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal) <
            (d - 2 * ε) ^ 2 * n ∨
          (d + 2 * ε) ^ 2 * n <
            ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal)) = L ∪ H := by
      ext w'
      simp only [L, H, ← hcommon, Finset.mem_filter, Finset.mem_union]
      tauto
    rw [hunion]
    calc
      ((L ∪ H).card : ENNReal) ≤ (L.card : ENNReal) + H.card := by
        exact_mod_cast Finset.card_union_le L H
      _ ≤ ε * W.card + ε * W.card := add_le_add hL hH
      _ = 2 * ε * W.card := by rw [← two_mul, mul_assoc]
  change (((W.product W).filter fun z =>
      ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal) <
          (d - 2 * ε) ^ 2 * n ∨
        (d + 2 * ε) ^ 2 * n <
          ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal)).card : ENNReal)
    ≤ 2 * ε * (W.card : ENNReal) ^ 2
  have htotal := FilteredProductRowCount W W (fun w w' =>
    ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal) <
        (d - 2 * ε) ^ 2 * n ∨
      (d + 2 * ε) ^ 2 * n <
        ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal))
  have htotal' :
      (((W.product W).filter fun z =>
        ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal) <
            (d - 2 * ε) ^ 2 * n ∨
          (d + 2 * ε) ^ 2 * n <
            ((U.filter fun u => G.Adj u z.1 ∧ G.Adj u z.2).card : ENNReal)).card : ENNReal) =
        ∑ w ∈ W, ((W.filter fun w' =>
          ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal) <
              (d - 2 * ε) ^ 2 * n ∨
            (d + 2 * ε) ^ 2 * n <
              ((U.filter fun u => G.Adj u w ∧ G.Adj u w').card : ENNReal)).card : ENNReal) := by
    exact_mod_cast htotal
  rw [htotal']
  calc
    _ ≤ ∑ _w ∈ W, 2 * ε * (W.card : ENNReal) := Finset.sum_le_sum hrow
    _ = 2 * ε * (W.card : ENNReal) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, pow_two]
      ac_rfl
