import Tablet.SuperRegularPair

-- [TABLET NODE: MatchingInducedLeftRowDeletion]
theorem MatchingInducedLeftRowDeletion :
    ∀ (m : ℕ) (ε ε' d : ENNReal),
      1 ≤ m → ε < ε' → ε' ≤ 1 → d ≤ 1 →
      ε + (2 : ENNReal) / m ≤ ε' →
      ε + 1 / (ε' * m) ≤ ε' →
      ∀ {V : Type*} [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (L R : Finset V) (x : V),
        Disjoint L R → x ∈ L → L.card = m + 1 →
        (R.card = m ∨ R.card = m + 1) →
        SuperRegularPair G L R ε d →
        SuperRegularPair G (L.erase x) R ε' d := by
-- BODY
  intro m ε ε' d hm hε hε' hd hslack _ V _ G _ L R x _ hx hL _ hsuper
  have hεle : ε ≤ ε' := hε.le
  have hεone : ε ≤ 1 := hεle.trans hε'
  have hm0 : (m : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm))
  have hmt : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hbudget : ε * m + 2 ≤ ε' * m := by
    have h := mul_le_mul_left hslack (m : ENNReal)
    rwa [add_mul, ENNReal.div_mul_cancel hm0 hmt] at h
  have hsize : ((L.erase x).card : ENNReal) = m := by
    simp only [Finset.card_erase_of_mem hx, hL, Nat.add_sub_cancel]
  have hLcast : (L.card : ENNReal) = (m : ENNReal) + 1 := by
    simp only [hL, Nat.cast_add, Nat.cast_one]
  have herror : ε * ((m : ENNReal) + 1) + 1 ≤ ε' * m := by
    calc
      ε * ((m : ENNReal) + 1) + 1 = ε * m + (ε + 1) := by
        rw [mul_add, mul_one, add_assoc]
      _ ≤ ε * m + 2 := by
        exact add_le_add le_rfl
          (by simpa only [one_add_one_eq_two] using add_le_add hεone (le_refl (1 : ENNReal)))
      _ ≤ ε' * m := hbudget
  have hthreshold : ε * ((m : ENNReal) + 1) ≤ ε' * m :=
    (le_add_right le_rfl).trans herror
  have hupper : (d + ε) * ((m : ENNReal) + 1) ≤ (d + ε') * m := by
    calc
      (d + ε) * ((m : ENNReal) + 1) = d * m + (ε * m + (d + ε)) := by
        rw [mul_add, mul_one, add_mul, add_assoc]
      _ ≤ d * m + (ε * m + 2) := by
        exact add_le_add le_rfl (add_le_add le_rfl
          (by simpa only [one_add_one_eq_two] using add_le_add hd hεone))
      _ ≤ d * m + ε' * m := add_le_add le_rfl hbudget
      _ = (d + ε') * m := (add_mul _ _ _).symm
  rcases hsuper with ⟨hreg, hleft, hright⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U hU Z hZ hUsize hZsize
    have hUold : ε * (L.card : ENNReal) < U.card := by
      rw [hLcast]
      exact hthreshold.trans_lt (by simpa only [hsize] using hUsize)
    have hZold : ε * (R.card : ENNReal) < Z.card :=
      (mul_le_mul_left hεle _).trans_lt hZsize
    obtain ⟨hlower, hupper⟩ :=
      hreg U (hU.trans (Finset.erase_subset x L)) Z hZ hUold hZold
    exact ⟨(tsub_le_tsub_left hεle d).trans hlower,
      hupper.trans (add_le_add le_rfl hεle)⟩
  · intro v hv
    obtain ⟨hlower, hupper⟩ := hleft v (Finset.mem_of_mem_erase hv)
    exact ⟨(mul_le_mul_left (tsub_le_tsub_left hεle d) _).trans hlower,
      hupper.trans (mul_le_mul_left (add_le_add le_rfl hεle) _)⟩
  · intro w hw
    obtain ⟨hlower, holdUpper⟩ := hright w hw
    have hcount : ((L.filter fun v => G.Adj v w).card : ENNReal) ≤
        (((L.erase x).filter fun v => G.Adj v w).card : ENNReal) + 1 := by
      have hnat : (L.filter fun v => G.Adj v w).card ≤
          ((L.erase x).filter fun v => G.Adj v w).card + 1 := by
        rw [Finset.filter_erase]
        by_cases hmem : x ∈ L.filter fun v => G.Adj v w
        · exact (Finset.card_erase_add_one hmem).symm.le
        · rw [Finset.erase_eq_of_notMem hmem]
          exact Nat.le_add_right _ _
      exact_mod_cast hnat
    have hcountUpper : (((L.erase x).filter fun v => G.Adj v w).card : ENNReal) ≤
        ((L.filter fun v => G.Adj v w).card : ENNReal) := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.erase_subset x L)))
    constructor
    · rw [hsize, ENNReal.sub_mul (fun _ _ => hmt), tsub_le_iff_right]
      rw [hLcast, ENNReal.sub_mul (fun _ _ => ENNReal.add_ne_top.mpr
        ⟨hmt, ENNReal.one_ne_top⟩), tsub_le_iff_right] at hlower
      calc
        d * (m : ENNReal) ≤ d * ((m : ENNReal) + 1) :=
          mul_le_mul_right (le_add_right le_rfl) d
        _ ≤ ((L.filter fun v => G.Adj v w).card : ENNReal) +
            ε * ((m : ENNReal) + 1) := hlower
        _ ≤ ((((L.erase x).filter fun v => G.Adj v w).card : ENNReal) + 1) +
            ε * ((m : ENNReal) + 1) := add_le_add hcount le_rfl
        _ = (((L.erase x).filter fun v => G.Adj v w).card : ENNReal) +
            (ε * ((m : ENNReal) + 1) + 1) := by rw [add_assoc, add_comm 1]
        _ ≤ (((L.erase x).filter fun v => G.Adj v w).card : ENNReal) + ε' * m :=
          add_le_add le_rfl herror
    · rw [hsize]
      exact hcountUpper.trans (holdUpper.trans (by simpa only [hLcast] using hupper))
