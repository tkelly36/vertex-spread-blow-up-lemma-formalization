import Tablet.LowerRegularPair
import Tablet.FilteredProductRowCount

-- [TABLET NODE: LowerRegularBadRows]
theorem LowerRegularBadRows {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L R S : Finset V) (ε d : ENNReal)
    (hreg : LowerRegularPair G L R ε d) (hS : S ⊆ R)
    (hsize : ε * R.card < S.card) :
    ((L.filter fun v => ((S.filter fun z => G.Adj v z).card : ENNReal) <
      (d - ε) * S.card).card : ENNReal) ≤ ε * L.card := by
-- BODY
  classical
  let T := L.filter fun v => ((S.filter fun z => G.Adj v z).card : ENNReal) <
    (d - ε) * S.card
  change (T.card : ENNReal) ≤ ε * L.card
  by_contra hbound
  have hTsize : ε * L.card < T.card := lt_of_not_ge hbound
  have hTzero : (T.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hTsize)
  have hSzero : (S.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hsize)
  have hTnonempty : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast
    ((zero_le _).trans_lt hTsize : (0 : ENNReal) < T.card))
  have hdenzero : (T.card : ENNReal) * S.card ≠ 0 := mul_ne_zero hTzero hSzero
  have hdenfinite : (T.card : ENNReal) * S.card ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  have hsum : (∑ v ∈ T, ((S.filter fun z => G.Adj v z).card : ENNReal)) <
      ∑ _v ∈ T, (d - ε) * S.card := by
    apply ENNReal.sum_lt_sum_of_nonempty hTnonempty
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hdensity : PairDensity G T S < d - ε := by
    unfold PairDensity
    apply (ENNReal.div_lt_iff (Or.inl hdenzero) (Or.inl hdenfinite)).mpr
    rw [FilteredProductRowCount T S G.Adj]
    simpa only [Nat.cast_sum, Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_comm,
      mul_left_comm] using hsum
  exact (not_lt_of_ge (hreg T (Finset.filter_subset _ _) S hS hTsize hsize)) hdensity
