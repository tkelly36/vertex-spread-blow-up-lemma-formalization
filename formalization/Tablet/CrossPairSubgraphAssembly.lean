import Tablet.SuperRegularPair
import Tablet.SuperRegularPairEmbedding

open scoped Classical

-- [TABLET NODE: CrossPairSubgraphAssembly]
theorem CrossPairSubgraphAssembly {V I : Type*}
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : SimpleGraph I)
    (f : V → I) (η c : ENNReal)
    (hpair : ∀ p q, R.Adj p q →
      ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
        F ≤ G ∧
        (∀ ⦃u v⦄, F.Adj u v →
          (f u = p ∧ f v = q) ∨ (f u = q ∧ f v = p)) ∧
        SuperRegularPair F (Finset.univ.filter fun v => f v = p)
          (Finset.univ.filter fun v => f v = q) η c) :
    ∃ G' : SimpleGraph V, ∃ _ : DecidableRel G'.Adj,
      G' ≤ G ∧
      (∀ ⦃u v⦄, G'.Adj u v → R.Adj (f u) (f v)) ∧
      (∀ p q, R.Adj p q →
        SuperRegularPair G' (Finset.univ.filter fun v => f v = p)
          (Finset.univ.filter fun v => f v = q) η c) := by
-- BODY
  classical
  let rank := Fintype.equivFin I
  let E := {pq : I × I // R.Adj pq.1 pq.2 ∧ rank pq.1 < rank pq.2}
  have hex : ∀ e : E, ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
      F ≤ G ∧ (∀ ⦃u v⦄, F.Adj u v →
        (f u = e.val.1 ∧ f v = e.val.2) ∨ (f u = e.val.2 ∧ f v = e.val.1)) ∧
      SuperRegularPair F (Finset.univ.filter fun v => f v = e.val.1)
        (Finset.univ.filter fun v => f v = e.val.2) η c := by
    intro e
    exact hpair e.val.1 e.val.2 e.property.1
  choose F hFdec hFG hFsupport hFreg using hex
  let G' : SimpleGraph V := {
    Adj := fun u v => ∃ e : E, (F e).Adj u v
    symm := by
      intro u v h
      obtain ⟨e, he⟩ := h
      exact ⟨e, (F e).symm he⟩
    loopless := by
      refine ⟨?_⟩
      intro v h
      obtain ⟨e, he⟩ := h
      exact (F e).loopless.irrefl v he }
  letI : DecidableRel G'.Adj := Classical.decRel _
  have hG'G : G' ≤ G := by
    intro u v h
    obtain ⟨e, he⟩ := h
    exact hFG e he
  have hG'support : ∀ ⦃u v⦄, G'.Adj u v → R.Adj (f u) (f v) := by
    intro u v h
    obtain ⟨e, he⟩ := h
    rcases hFsupport e he with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using e.property.1
    · simpa only [hu, hv] using R.symm e.property.1
  have hagree : ∀ (p q : I) (hpq : R.Adj p q) (hlt : rank p < rank q),
      let e₀ : E := ⟨(p, q), hpq, hlt⟩
      ∀ u ∈ (Finset.univ.filter fun v => f v = p),
        ∀ v ∈ (Finset.univ.filter fun v => f v = q),
          G'.Adj u v ↔ (F e₀).Adj u v := by
    intro p q hpq hlt e₀ u hu v hv
    have hup := (Finset.mem_filter.mp hu).2
    have hvq := (Finset.mem_filter.mp hv).2
    constructor
    · intro h
      obtain ⟨e, he⟩ := h
      rcases hFsupport e he with ⟨heu, hev⟩ | ⟨heu, hev⟩
      · have heq : e = e₀ := Subtype.ext (Prod.ext (heu.symm.trans hup) (hev.symm.trans hvq))
        simpa only [heq] using he
      · have hreverse : rank q < rank p := by
          simpa only [hev.symm.trans hvq, heu.symm.trans hup] using e.property.2
        exact (not_lt_of_ge hlt.le hreverse).elim
    · intro h
      exact ⟨e₀, h⟩
  have hswap : ∀ (K : SimpleGraph V) [DecidableRel K.Adj] (U W : Finset V),
      SuperRegularPair K U W η c → SuperRegularPair K W U η c := by
    intro K _ U W h
    have hdensity (S T : Finset V) : PairDensity K S T = PairDensity K T S := by
      have hcount : ((S.product T).filter fun p => K.Adj p.1 p.2).card =
          ((T.product S).filter fun p => K.Adj p.1 p.2).card := by
        apply Finset.card_bij (fun p _ => p.swap)
        · intro p hp
          obtain ⟨hpST, hpAdj⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hpST
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpT, hpS⟩, K.symm hpAdj⟩
        · intro p _ q _ hpq
          exact Prod.swap_injective hpq
        · intro p hp
          obtain ⟨hpTS, hpAdj⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpT, hpS⟩ := Finset.mem_product.mp hpTS
          exact ⟨p.swap, Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hpS, hpT⟩, K.symm hpAdj⟩, rfl⟩
      simp only [PairDensity, hcount, mul_comm]
    refine ⟨?_, ?_, ?_⟩
    · intro S hS T hT hScard hTcard
      simpa only [hdensity S T] using h.1 T hT S hS hTcard hScard
    · intro w hw
      simpa only [K.adj_comm] using h.2.2 w hw
    · intro u hu
      simpa only [K.adj_comm] using h.2.1 u hu
  refine ⟨G', inferInstance, hG'G, @hG'support, ?_⟩
  intro p q hpq
  have hne : rank p ≠ rank q := fun h => R.ne_of_adj hpq (rank.injective h)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · let e₀ : E := ⟨(p, q), hpq, hlt⟩
    letI : DecidableRel (F e₀).Adj := hFdec e₀
    simpa only [Finset.image_id] using
      SuperRegularPairEmbedding id Function.injective_id (F e₀) G' _ _ η c
        (hagree p q hpq hlt) (hFreg e₀)
  · let e₀ : E := ⟨(q, p), R.symm hpq, hlt⟩
    letI : DecidableRel (F e₀).Adj := hFdec e₀
    have hqp : SuperRegularPair G' (Finset.univ.filter fun v => f v = q)
        (Finset.univ.filter fun v => f v = p) η c := by
      simpa only [Finset.image_id] using
        SuperRegularPairEmbedding id Function.injective_id (F e₀) G' _ _ η c
          (hagree q p (R.symm hpq) hlt) (hFreg e₀)
    exact hswap G' _ _ hqp
