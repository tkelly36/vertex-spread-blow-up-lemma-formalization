import Tablet.SuperRegularPair
import Tablet.CrossEdgeRetentionCounts
import Tablet.RetentionBadEventUnion
import Tablet.IndependentEdgeSample
import Tablet.IndependentUnequalEdgeSampleLaw
import Tablet.NearEqualRetentionThreshold
import Tablet.ThinningCountInterval
import Tablet.PairDensity
import Tablet.ThinningRealParameters

open MeasureTheory
open scoped NNReal

-- [TABLET NODE: QuantitativeSuperRegularThinning]
theorem QuantitativeSuperRegularThinning :
    ∀ β D ρ η ξ : ENNReal,
      0 < β → β < η → 0 < ρ → ρ < D → D ≤ 1 →
      0 < ξ → 4 * ((ρ / D) * β + ξ) ≤ η → 10 * η < ρ →
      ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V),
        Disjoint L R → n₀ ≤ L.card → n₀ ≤ R.card →
        L.card ≤ R.card + 1 → R.card ≤ L.card + 1 →
        SuperRegularPair G L R β D →
        ∃ G' : SimpleGraph V, G' ≤ G ∧
          @SuperRegularPair V _ G' (Classical.decRel _) L R η ρ := by
-- BODY
  classical
  intro β D ρ η ξ hβ hβη hρ hρD hD hξ hbudget hsmall
  obtain ⟨hDtop, hβtop, hρtop, hηtop, hξtop, hηρ, hβD, hηpos, hξpos, q, hq, hqd, herr⟩ :=
    ThinningRealParameters β D ρ η ξ hβ hβη hρ hρD hD hξ hbudget hsmall
  obtain ⟨n₀, hn₀, hn⟩ := NearEqualRetentionThreshold ξ.toReal η.toReal hξpos hηpos
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ L R hLR hL hR hnearL hnearR hG
  have hLpos : 0 < L.card := lt_of_lt_of_le (by omega) hL
  have hRpos : 0 < R.card := lt_of_lt_of_le (by omega) hR
  have hlaw := IndependentUnequalEdgeSampleLaw (fun _ : V × V => q) (fun _ => hq)
  have hprob : IsProbabilityMeasure (IndependentEdgeSample (V × V) q hq) := by
    simpa only [IndependentEdgeSample] using hlaw.1
  letI := hprob
  have hbad := RetentionBadEventUnion G L R q hq ξ.toReal hξpos η
    (hβ.trans hβη) hηtop hLpos hRpos
  have htotal := hn L.card R.card hL hR hnearL hnearR
  have hex : ∃ ω : V × V → Bool, RetentionCountControl G L R q ξ.toReal η ω := by
    by_contra hnone
    have he : {ω : V × V → Bool | ¬ RetentionCountControl G L R q ξ.toReal η ω} =
        Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun h => hnone ⟨ω, h⟩
    rw [he, measure_univ] at hbad
    exact (not_le_of_gt htotal) hbad
  obtain ⟨ω, hω⟩ := hex
  obtain ⟨hsub, hrect, hleft, hright⟩ := CrossEdgeRetentionCounts G L R hLR ω
  refine ⟨CrossEdgeRetention G L R ω, hsub, ?_⟩
  have htransfer := ThinningCountInterval D β ρ η hDtop hβtop hρtop hηtop
    hβD hηρ.le q ξ.toReal q.coe_nonneg hqd herr
  change RegularPair (CrossEdgeRetention G L R ω) L R η ρ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro U hUL W hWR hUth hWth
    have hUpos : 0 < U.card := by
      have : (0 : ENNReal) < U.card := lt_of_le_of_lt (zero_le _) hUth
      exact_mod_cast this
    have hWpos : 0 < W.card := by
      have : (0 : ENNReal) < W.card := lt_of_le_of_lt (zero_le _) hWth
      exact_mod_cast this
    have hUβ : β * (L.card : ENNReal) < U.card :=
      lt_of_le_of_lt (mul_le_mul_left hβη.le _) hUth
    have hWβ : β * (R.card : ENNReal) < W.card :=
      lt_of_le_of_lt (mul_le_mul_left hβη.le _) hWth
    have hm : (U.card : ENNReal) * W.card ≠ 0 := by
      simp only [mul_ne_zero_iff, Nat.cast_ne_zero]
      exact ⟨hUpos.ne', hWpos.ne'⟩
    have hmt : (U.card : ENNReal) * W.card ≠ ⊤ := by finiteness
    have hold := hG.1 U hUL W hWR hUβ hWβ
    unfold PairDensity at hold
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm) (Or.inl hmt),
      ENNReal.div_le_iff hm hmt] at hold
    have hdev := hω.2.2 U hUL W hWR hUth hWth
    unfold PairDensity
    rw [ENNReal.le_div_iff_mul_le (Or.inl hm) (Or.inl hmt),
      ENNReal.div_le_iff hm hmt, ← Nat.cast_mul]
    rw [hrect U hUL W hWR]
    apply htransfer (U.card * W.card)
      ((U.product W).filter fun p => G.Adj p.1 p.2).card
    · simpa only [Nat.cast_mul] using hold
    · simpa only [Nat.cast_mul] using hdev
  · intro v hv
    have hcard : ((({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2).card =
        (R.filter fun w => G.Adj v w).card := by
      have he : ((({v} : Finset V).product R).filter fun p => G.Adj p.1 p.2) =
          ({v} : Finset V).product (R.filter fun w => G.Adj v w) := by
        ext p
        simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton]
        aesop
      rw [he]
      simp only [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_singleton, one_mul]
    have hdev := hω.1 v hv
    dsimp only at hdev
    rw [hcard] at hdev
    rw [hleft v hv]
    exact htransfer R.card (R.filter fun w => G.Adj v w).card _ (hG.2.1 v hv) hdev
  · intro w hw
    have hcard : ((L.product {w}).filter fun p => G.Adj p.1 p.2).card =
        (L.filter fun v => G.Adj v w).card := by
      have he : ((L.product {w}).filter fun p => G.Adj p.1 p.2) =
          (L.filter fun v => G.Adj v w).product {w} := by
        ext p
        simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hv, rfl⟩, hp⟩
          exact ⟨⟨hv, hp⟩, rfl⟩
        · rintro ⟨⟨hv, hp⟩, rfl⟩
          exact ⟨⟨hv, rfl⟩, hp⟩
      rw [he]
      simp only [Finset.product_eq_sprod, Finset.card_product,
        Finset.card_singleton, mul_one]
    have hdev := hω.2.1 w hw
    dsimp only at hdev
    rw [hcard] at hdev
    rw [hright w hw]
    exact htransfer L.card (L.filter fun v => G.Adj v w).card _ (hG.2.2 w hw) hdev
