import Tablet.OneIndexBadPairCounting
import Tablet.RegularityAfterDensityLoss
import Tablet.SuperRegularPair
import Tablet.SimultaneousGoodEdgeGraph
import Tablet.RegularPairLowerTail
import Tablet.RegularPairUpperTail
import Tablet.CodegreeWindowTransfer
import Tablet.SmallNeighborhoodCodegreeWindow

-- [TABLET NODE: NearEqualVaryingGoodEdgeSuperRegularity]
theorem NearEqualVaryingGoodEdgeSuperRegularity :
    ∀ {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]
      (F₁₂ : SimpleGraph V) (F₁₃ F₂₃ : K → SimpleGraph V)
      [DecidableRel F₁₂.Adj] [∀ k, DecidableRel (F₁₃ k).Adj]
      [∀ k, DecidableRel (F₂₃ k).Adj]
      (W₁ W₂ : Finset V) (W₃ : K → Finset V) (m : ℕ)
      (ε₀ η δ : ENNReal) (ε d₁₃ d₂₃ : K → ENNReal),
      (h₁₂ : Disjoint W₁ W₂) →
      (∀ k, Disjoint W₁ (W₃ k) ∧ Disjoint W₂ (W₃ k)) →
      W₁.card = m → W₂.card = m →
      (∀ k, (W₃ k).card + 1 = m ∨ (W₃ k).card = m ∨ (W₃ k).card = m + 1) →
      ε₀ ≤ η → (∀ k, ε k ≤ 1 ∧ 2 * (ε k) ^ (2 : ℝ)⁻¹ ≤ η) →
      ε₀ + ∑ k, (ε k) ^ (2 : ℝ)⁻¹ ≤ η →
      ε₀ + 2 * ∑ k, ε k ≤ η →
      (∀ k, 2 * ε k < d₁₃ k ∧ 2 * ε k < d₂₃ k) →
      (∀ k, d₁₃ k ≤ 1 ∧ d₂₃ k ≤ 1) →
      SuperRegularPair F₁₂ W₁ W₂ ε₀ δ →
      (∀ k, SuperRegularPair (F₁₃ k) W₁ (W₃ k) (ε k) (d₁₃ k)) →
      (∀ k, SuperRegularPair (F₂₃ k) W₂ (W₃ k) (ε k) (d₂₃ k)) →
      let F := SimultaneousGoodEdgeGraph F₁₂ F₁₃ F₂₃ W₁ W₂ h₁₂ W₃ ε d₁₃ d₂₃
      letI : DecidableRel F.Adj := Classical.decRel _
      SuperRegularPair F W₁ W₂ η δ := by
-- BODY
  intro V K _ _ _ F₁₂ F₁₃ F₂₃ _ _ _ W₁ W₂ W₃ m ε₀ η δ ε d₁₃ d₂₃
    h₁₂ _hdisj hW₁ hW₂ hnear hε₀ hε hregsum hdegsum _hpositive hd hF₁₂ hF₁₃ hF₂₃
  classical
  let F := SimultaneousGoodEdgeGraph F₁₂ F₁₃ F₂₃ W₁ W₂ h₁₂ W₃ ε d₁₃ d₂₃
  letI : DecidableRel F.Adj := Classical.decRel _
  change SuperRegularPair F W₁ W₂ η δ
  let good (k : K) (x v : V) :=
    (d₁₃ k * d₂₃ k - 2 * ε k) * (W₃ k).card ≤
      (((W₃ k).filter fun z => (F₁₃ k).Adj x z ∧ (F₂₃ k).Adj v z).card : ENNReal) ∧
    (((W₃ k).filter fun z => (F₁₃ k).Adj x z ∧ (F₂₃ k).Adj v z).card : ENNReal) ≤
      (d₁₃ k * d₂₃ k + 2 * ε k) * (W₃ k).card
  have hchar (x : V) (hx : x ∈ W₁) (v : V) (hv : v ∈ W₂) :
      F.Adj x v ↔ F₁₂.Adj x v ∧ ∀ k, good k x v := by
    change (x ≠ v ∧
      ((x ∈ W₁ ∧ v ∈ W₂ ∧ F₁₂.Adj x v ∧ ∀ k, good k x v) ∨
       (v ∈ W₁ ∧ x ∈ W₂ ∧ F₁₂.Adj v x ∧ ∀ k, good k v x))) ↔ _
    constructor
    · rintro ⟨_, h | h⟩
      · exact ⟨h.2.2.1, h.2.2.2⟩
      · exact False.elim (Finset.disjoint_left.mp h₁₂ h.1 hv)
    · intro h
      exact ⟨F₁₂.ne_of_adj h.1, Or.inl ⟨hx, hv, h.1, h.2⟩⟩
  have hcharRight (v : V) (hv : v ∈ W₂) (x : V) (hx : x ∈ W₁) :
      F.Adj v x ↔ F₁₂.Adj v x ∧ ∀ k, good k x v := by
    rw [F.adj_comm v x, F₁₂.adj_comm v x]
    exact hchar x hx v hv
  -- A finite union bound for the original elements discarded by any test.
  have hcount {A : Type _} [DecidableEq A] (S : Finset A)
      (edge : A → Prop) (test : K → A → Prop)
      [DecidablePred edge] [∀ k, DecidablePred (test k)] :
      ((S.filter edge).card : ENNReal) ≤
        ((S.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) +
          ∑ k, ((S.filter fun a => ¬ test k a).card : ENNReal) := by
    as_aux_lemma =>
      let E := S.filter edge
      let D := E.filter fun a => ¬ ∀ k, test k a
      have hpartition : (S.filter edge).card =
          (S.filter fun a => edge a ∧ ∀ k, test k a).card + D.card := by
        simpa only [E, D, Finset.filter_filter] using
          (Finset.card_filter_add_card_filter_not (s := E) (fun a => ∀ k, test k a)).symm
      have hsub : D ⊆ Finset.univ.biUnion (fun k => S.filter fun a => ¬ test k a) := by
        intro a ha
        obtain ⟨haE, hanot⟩ := Finset.mem_filter.mp ha
        obtain ⟨k, hk⟩ := not_forall.mp hanot
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haE).1, hk⟩⟩
      have hD : D.card ≤ ∑ k, (S.filter fun a => ¬ test k a).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      rw [hpartition, Nat.cast_add]
      apply add_le_add le_rfl
      exact_mod_cast hD
  have hpartner (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (L R T : Finset V) (ε p q : ENNReal)
      (hε : ε ≤ 1) (hp : p ≤ 1) (hq : q ≤ 1)
      (hG : SuperRegularPair G L T ε p) (hH : RegularPair H R T ε q) :
      ∀ x ∈ L,
        ((R.filter fun v => ¬ ((p * q - 2 * ε) * T.card ≤
          ((T.filter fun z => G.Adj x z ∧ H.Adj v z).card : ENNReal) ∧
          ((T.filter fun z => G.Adj x z ∧ H.Adj v z).card : ENNReal) ≤
            (p * q + 2 * ε) * T.card)).card : ENNReal) ≤ 2 * ε * R.card := by
    as_aux_lemma =>
      intro x hx
      by_cases hT : T = ∅
      · simp [hT]
      have hk : T.card ≠ 0 := fun hz => hT (Finset.card_eq_zero.mp hz)
      let C (v : V) := (T.filter fun z => G.Adj x z ∧ H.Adj v z).card
      let bad (v : V) := ¬ ((p * q - 2 * ε) * T.card ≤ (C v : ENNReal) ∧
        (C v : ENNReal) ≤ (p * q + 2 * ε) * T.card)
      change ((R.filter bad).card : ENNReal) ≤ 2 * ε * R.card
      let S := T.filter fun z => G.Adj x z
      have hS : S ⊆ T := Finset.filter_subset _ _
      have hSk : S.card ≤ T.card := Finset.card_le_card hS
      obtain ⟨halower, haupper⟩ := hG.2.1 x hx
      change (p - ε) * T.card ≤ (S.card : ENNReal) at halower
      change (S.card : ENNReal) ≤ (p + ε) * T.card at haupper
      have hC (v : V) : (S.filter fun z => H.Adj v z).card = C v := by
        simp only [S, C, Finset.filter_filter]
      have hca (v : V) : C v ≤ S.card := by
        rw [← hC v]
        exact Finset.card_filter_le _ _
      by_cases hsmall : (S.card : ENNReal) ≤ ε * T.card
      · have hempty : R.filter bad = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro v _hv hbad
          exact hbad (SmallNeighborhoodCodegreeWindow ε p q T.card S.card
            (C v) hk hε hp hq halower hsmall (hca v))
        simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_le]
      · have hlarge : ε * T.card < S.card := lt_of_not_ge hsmall
        let Tminus := R.filter fun v =>
          ((S.filter fun z => H.Adj v z).card : ENNReal) < (q - ε) * S.card
        let Tplus := R.filter fun v =>
          (q + ε) * S.card < ((S.filter fun z => H.Adj v z).card : ENNReal)
        have hminus : (Tminus.card : ENNReal) ≤ ε * R.card :=
          RegularPairLowerTail H R T S ε q hε hq hH hS hlarge
        have hplus : (Tplus.card : ENNReal) ≤ ε * R.card :=
          RegularPairUpperTail H R T S ε q hε hq hH hS hlarge
        have hsubset : R.filter bad ⊆ Tminus ∪ Tplus := by
          intro v hv
          obtain ⟨hvR, hvbad⟩ := Finset.mem_filter.mp hv
          by_cases hm : v ∈ Tminus
          · exact Finset.mem_union_left _ hm
          by_cases ht : v ∈ Tplus
          · exact Finset.mem_union_right _ ht
          have hlower : (q - ε) * S.card ≤ (C v : ENNReal) := by
            have hnot : ¬ ((S.filter fun z => H.Adj v z).card : ENNReal) <
                (q - ε) * S.card := by
              intro hlt
              exact hm (Finset.mem_filter.mpr ⟨hvR, hlt⟩)
            simpa only [hC v] using le_of_not_gt hnot
          have hupper : (C v : ENNReal) ≤ (q + ε) * S.card := by
            have hnot : ¬ (q + ε) * S.card <
                ((S.filter fun z => H.Adj v z).card : ENNReal) := by
              intro hlt
              exact ht (Finset.mem_filter.mpr ⟨hvR, hlt⟩)
            simpa only [hC v] using le_of_not_gt hnot
          exact False.elim (hvbad (CodegreeWindowTransfer ε p q T.card S.card
            (C v) hε hp hq hSk halower haupper hlower hupper))
        calc
          ((R.filter bad).card : ENNReal) ≤ (Tminus ∪ Tplus).card := by
            exact_mod_cast Finset.card_le_card hsubset
          _ ≤ (Tminus.card : ENNReal) + Tplus.card := by
            exact_mod_cast Finset.card_union_le Tminus Tplus
          _ ≤ ε * R.card + ε * R.card := add_le_add hminus hplus
          _ = 2 * ε * R.card := by ring
  have hrow (x : V) (hx : x ∈ W₁) (k : K) :
      ((W₂.filter fun v => ¬ good k x v).card : ENNReal) ≤ 2 * ε k * W₂.card :=
    hpartner (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) (ε k)
      (d₁₃ k) (d₂₃ k) (hε k).1 (hd k).1 (hd k).2 (hF₁₃ k) (hF₂₃ k).1 x hx
  have hcol (v : V) (hv : v ∈ W₂) (k : K) :
      ((W₁.filter fun x => ¬ good k x v).card : ENNReal) ≤ 2 * ε k * W₁.card := by
    have h := hpartner (F₂₃ k) (F₁₃ k) W₂ W₁ (W₃ k) (ε k)
      (d₂₃ k) (d₁₃ k) (hε k).1 (hd k).2 (hd k).1 (hF₂₃ k) (hF₁₃ k).1 v hv
    simpa only [good, mul_comm (d₂₃ k) (d₁₃ k), and_comm] using h
  have hdegree (A : Finset V) (edge : V → Prop) (test : K → V → Prop)
      [DecidablePred edge] [∀ k, DecidablePred (test k)]
      (hlower : (δ - ε₀) * A.card ≤ ((A.filter edge).card : ENNReal))
      (hupper : ((A.filter edge).card : ENNReal) ≤ (δ + ε₀) * A.card)
      (hbad : ∀ k, ((A.filter fun a => ¬ test k a).card : ENNReal) ≤ 2 * ε k * A.card) :
      (δ - η) * A.card ≤ ((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) ∧
      ((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) ≤ (δ + η) * A.card := by
    as_aux_lemma =>
      have hsum : (∑ k, ((A.filter fun a => ¬ test k a).card : ENNReal)) ≤
          (2 * ∑ k, ε k) * A.card := by
        calc
          _ ≤ ∑ k, 2 * ε k * A.card := Finset.sum_le_sum fun k _ => hbad k
          _ = (2 * ∑ k, ε k) * A.card := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      have hlost := (hcount A edge test).trans (add_le_add le_rfl hsum)
      constructor
      · rw [ENNReal.sub_mul (fun _ _ => ENNReal.natCast_ne_top A.card)]
        apply tsub_le_iff_right.mpr
        have hbase : δ * A.card ≤ ((A.filter edge).card : ENNReal) + ε₀ * A.card := by
          apply tsub_le_iff_right.mp
          simpa only [ENNReal.sub_mul (fun _ _ => ENNReal.natCast_ne_top A.card)] using hlower
        calc
          δ * A.card ≤ ((A.filter edge).card : ENNReal) + ε₀ * A.card := hbase
          _ ≤ (((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) +
              (2 * ∑ k, ε k) * A.card) + ε₀ * A.card := add_le_add hlost le_rfl
          _ = ((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) +
              (ε₀ + 2 * ∑ k, ε k) * A.card := by ring
          _ ≤ ((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) + η * A.card :=
            add_le_add le_rfl (mul_le_mul_right' hdegsum _)
      · have hsub : A.filter (fun a => edge a ∧ ∀ k, test k a) ⊆ A.filter edge := by
          intro a ha
          obtain ⟨haA, hae, _⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨haA, hae⟩
        have hc : ((A.filter fun a => edge a ∧ ∀ k, test k a).card : ENNReal) ≤
            (A.filter edge).card := by exact_mod_cast Finset.card_le_card hsub
        exact hc.trans (hupper.trans (mul_le_mul_right' (add_le_add le_rfl hε₀) _))
  refine ⟨?_, ?_, ?_⟩
  · apply RegularityAfterDensityLoss F₁₂ F W₁ W₂ ε₀ δ η
      (∑ k, (ε k) ^ (2 : ℝ)⁻¹) hε₀ hregsum hF₁₂.1
    intro U hU Z hZ hsizeU hsizeZ
    have heq : (U.product Z).filter (fun p => F.Adj p.1 p.2) =
        (U.product Z).filter (fun p => F₁₂.Adj p.1 p.2 ∧ ∀ k, good k p.1 p.2) := by
      apply Finset.filter_congr
      intro p hp
      obtain ⟨hpU, hpZ⟩ := Finset.mem_product.mp hp
      exact hchar p.1 (hU hpU) p.2 (hZ hpZ)
    have hsub : (U.product Z).filter (fun p => F.Adj p.1 p.2) ⊆
        (U.product Z).filter (fun p => F₁₂.Adj p.1 p.2) := by
      intro p hp
      obtain ⟨hpUZ, hpF⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpU, hpZ⟩ := Finset.mem_product.mp hpUZ
      exact Finset.mem_filter.mpr ⟨hpUZ, ((hchar p.1 (hU hpU) p.2 (hZ hpZ)).mp hpF).1⟩
    have hmono : PairDensity F U Z ≤ PairDensity F₁₂ U Z := by
      apply ENNReal.div_le_div_right
      exact_mod_cast Finset.card_le_card hsub
    refine ⟨hmono, ?_⟩
    let den : ENNReal := (U.card : ENNReal) * Z.card
    have hbad (k : K) :
        (((U.product Z).filter fun p => ¬ good k p.1 p.2).card : ENNReal) / den ≤
          (ε k) ^ (2 : ℝ)⁻¹ := by
      apply OneIndexBadPairCounting (F₁₃ k) (F₂₃ k) W₁ W₂ (W₃ k) m (ε k)
        (d₁₃ k) (d₂₃ k) hW₁ hW₂ (hnear k) (hε k).1 (hd k).1 (hd k).2
        (hF₁₃ k) (hF₂₃ k) U hU Z hZ
      · exact (mul_le_mul_right' (hε k).2 (m : ENNReal)).trans_lt (by simpa only [hW₁] using hsizeU)
      · exact (mul_le_mul_right' (hε k).2 (m : ENNReal)).trans_lt (by simpa only [hW₂] using hsizeZ)
    have hsum : (∑ k, (((U.product Z).filter fun p => ¬ good k p.1 p.2).card : ENNReal)) / den ≤
        ∑ k, (ε k) ^ (2 : ℝ)⁻¹ := by
      simpa only [div_eq_mul_inv, Finset.sum_mul] using Finset.sum_le_sum (fun k _ => hbad k)
    have hbound := ENNReal.div_le_div_right
      (hcount (U.product Z) (fun p => F₁₂.Adj p.1 p.2) (fun k p => good k p.1 p.2)) den
    rw [← heq, ENNReal.add_div] at hbound
    have hloss : PairDensity F₁₂ U Z ≤ PairDensity F U Z + ∑ k, (ε k) ^ (2 : ℝ)⁻¹ :=
      hbound.trans (add_le_add le_rfl hsum)
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using hloss
  · intro x hx
    have heq : W₂.filter (fun v => F.Adj x v) =
        W₂.filter (fun v => F₁₂.Adj x v ∧ ∀ k, good k x v) := by
      exact Finset.filter_congr fun v hv => hchar x hx v hv
    rw [heq]
    exact hdegree W₂ (fun v => F₁₂.Adj x v) (fun k v => good k x v)
      (hF₁₂.2.1 x hx).1 (hF₁₂.2.1 x hx).2 (hrow x hx)
  · intro v hv
    have heq : W₁.filter (fun x => F.Adj x v) =
        W₁.filter (fun x => F₁₂.Adj x v ∧ ∀ k, good k x v) := by
      apply Finset.filter_congr
      intro x hx
      simpa only [F.adj_comm v x, F₁₂.adj_comm v x] using hcharRight v hv x hx
    rw [heq]
    exact hdegree W₁ (fun x => F₁₂.Adj x v) (fun k x => good k x v)
      (hF₁₂.2.2 v hv).1 (hF₁₂.2.2 v hv).2 (hcol v hv)
