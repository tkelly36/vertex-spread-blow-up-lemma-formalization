import Tablet.CandidacyLowerSuperRegular
import Tablet.UpdatedCandidacy
import Tablet.ExceptionalLeftLowerSuperRegular

-- [TABLET NODE: RebalancingResidualCandidacy]
theorem RebalancingResidualCandidacy {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel H.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X : Finset VH) (f : PartialCompatibleEmbedding B A X)
    (Br : BlowUpInstance r {x : VH // x ∉ X} {v : VG // v ∉ X.image f.toFun}
      (H.induce {x : VH | x ∉ X}) (G.induce {v : VG | v ∉ X.image f.toFun}) R)
    (Ar : CandidacySystem Br) (m : ℕ) (ε d ε' d' L J η rho : ENNReal)
    (hsource : ∀ x, Br.sourceCluster x = B.sourceCluster x.1)
    (hhost : ∀ v, Br.hostCluster v = B.hostCluster v.1)
    (hallowed : ∀ x v, Ar.allowed x v ↔ (UpdatedCandidacy B A X f).allowed x.1 v.1)
    (hleft : ∀ i, Fintype.card {x : {x : VH // x ∉ X} // Br.sourceCluster x = i} = m)
    (hright : ∀ i, Fintype.card {v : {v : VG // v ∉ X.image f.toFun} //
      Br.hostCluster v = i} = m)
    (hEq : ∀ i, Fintype.card {x : VH // B.sourceCluster x = i} =
      Fintype.card {v : VG // B.hostCluster v = i})
    (hSR : CandidacyLowerSuperRegular B A ε d)
    (hX : ∀ i, ((X.filter fun x => B.sourceCluster x = i).card : ENNReal) ≤ L)
    (himage : ∀ i, (((X.image f.toFun).filter fun v => B.hostCluster v = i).card :
      ENNReal) ≤ L)
    (hbuffer : ∀ i, (((Finset.univ.filter fun x => x ∉ X ∧ ∃ y ∈ X, H.Adj x y).filter
      fun x => B.sourceCluster x = i).card : ENNReal) ≤ J)
    (hJ : J ≤ η * m) (hε' : 0 < ε') (hε'top : ε' < ⊤)
    (hthreshold : ∀ i, ε * Fintype.card {v : VG // B.hostCluster v = i} ≤ ε' * m)
    (hdensity : (d' - ε') + η / ε' ≤ d - ε)
    (hdegree : ∀ i, (d' - ε') * m ≤
      (d - ε) * Fintype.card {v : VG // B.hostCluster v = i} - L - J)
    (hrho : (d' - ε') * m ≤ rho)
    (hreserve : ∀ x, x ∉ X → (∃ y ∈ X, H.Adj x y) →
      rho ≤ Set.ncard {v : VG | (UpdatedCandidacy B A X f).allowed x v}) :
    CandidacyLowerSuperRegular Br Ar ε' d' := by
-- BODY
  classical
  let left (P : VH → Prop) : Finset (VH ⊕ VG) :=
    Finset.univ.filter fun z => ∃ x, z = Sum.inl x ∧ P x
  let right (P : VG → Prop) : Finset (VH ⊕ VG) :=
    Finset.univ.filter fun z => ∃ v, z = Sum.inr v ∧ P v
  have mem_left (P : VH → Prop) (z) : z ∈ left P ↔
      ∃ x, z = Sum.inl x ∧ P x := by
    simp only [left, Finset.mem_filter, Finset.mem_univ, true_and]
  have mem_right (P : VG → Prop) (z) : z ∈ right P ↔
      ∃ v, z = Sum.inr v ∧ P v := by
    simp only [right, Finset.mem_filter, Finset.mem_univ, true_and]
  have left_map (P : VH → Prop) : left P =
      (Finset.univ.filter P).map Function.Embedding.inl := by
    ext z
    cases z <;> simp [left]
  have right_map (P : VG → Prop) : right P =
      (Finset.univ.filter P).map Function.Embedding.inr := by
    ext z
    cases z <;> simp [right]
  have left_card (P : VH → Prop) :
      (left P).card = (Finset.univ.filter P).card := by
    rw [left_map, Finset.card_map]
  have right_card (P : VG → Prop) :
      (right P).card = (Finset.univ.filter P).card := by
    rw [right_map, Finset.card_map]
  let Aup := UpdatedCandidacy B A X f
  let g₀ : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
    ∃ x v, p = Sum.inl x ∧ q = Sum.inr v ∧ A.allowed x v
  let g : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
    ∃ x v, p = Sum.inl x ∧ q = Sum.inr v ∧ Aup.allowed x v
  letI : DecidableRel g₀.Adj := Classical.decRel _
  letI : DecidableRel g.Adj := Classical.decRel _
  have adj₀ (x : VH) (v : VG) :
      g₀.Adj (Sum.inl x) (Sum.inr v) ↔ A.allowed x v := by
    simp [g₀, SimpleGraph.fromRel]
  have adj (x : VH) (v : VG) :
      g.Adj (Sum.inl x) (Sum.inr v) ↔ Aup.allowed x v := by
    simp [g, SimpleGraph.fromRel]
  let e : ({x : VH // x ∉ X} ⊕ {v : VG // v ∉ X.image f.toFun}) ↪ (VH ⊕ VG) :=
    (Function.Embedding.subtype _).sumMap (Function.Embedding.subtype _)
  let gr : SimpleGraph ({x : VH // x ∉ X} ⊕ {v : VG // v ∉ X.image f.toFun}) :=
    SimpleGraph.fromRel fun p q =>
      ∃ x v, p = Sum.inl x ∧ q = Sum.inr v ∧ Ar.allowed x v
  letI : DecidableRel gr.Adj := Classical.decRel _
  have adjr (x) (v) : gr.Adj (Sum.inl x) (Sum.inr v) ↔ Ar.allowed x v := by
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, h | h⟩
      · obtain ⟨x', v', hx, hv, ha⟩ := h
        cases Sum.inl.inj hx
        cases Sum.inr.inj hv
        exact ha
      · obtain ⟨x', v', hx, _, _⟩ := h
        cases hx
    · exact fun h => ⟨Sum.inl_ne_inr, Or.inl ⟨x, v, rfl, rfl, h⟩⟩
  have reflect (p q) : gr.Adj p q ↔ g.Adj (e p) (e q) := by
    cases p with
    | inl x =>
      cases q with
      | inl y => simp [gr, g, e, SimpleGraph.fromRel]
      | inr v =>
        change gr.Adj (Sum.inl x) (Sum.inr v) ↔
          g.Adj (Sum.inl x.1) (Sum.inr v.1)
        rw [adjr, adj]
        exact hallowed x v
    | inr v =>
      cases q with
      | inl x =>
        rw [gr.adj_comm, g.adj_comm]
        change gr.Adj (Sum.inl x) (Sum.inr v) ↔
          g.Adj (Sum.inl x.1) (Sum.inr v.1)
        rw [adjr, adj]
        exact hallowed x v
      | inr w => simp [gr, g, e, SimpleGraph.fromRel]
  intro i
  let L₀ := left (fun x => B.sourceCluster x = i)
  let Q₀ := right (fun v => B.hostCluster v = i)
  let DL := left (fun x => x ∈ X ∧ B.sourceCluster x = i)
  let DQ := right (fun v => v ∈ X.image f.toFun ∧ B.hostCluster v = i)
  let E := left (fun x => x ∉ X ∧ (∃ y ∈ X, H.Adj x y) ∧ B.sourceCluster x = i)
  let lr : Finset ({x : VH // x ∉ X} ⊕ {v : VG // v ∉ X.image f.toFun}) :=
    Finset.univ.filter fun z => ∃ x, z = Sum.inl x ∧ Br.sourceCluster x = i
  let qr : Finset ({x : VH // x ∉ X} ⊕ {v : VG // v ∉ X.image f.toFun}) :=
    Finset.univ.filter fun z => ∃ v, z = Sum.inr v ∧ Br.hostCluster v = i
  have mem_lr (z) : z ∈ lr ↔ ∃ x, z = Sum.inl x ∧ Br.sourceCluster x = i := by
    simp only [lr, Finset.mem_filter, Finset.mem_univ, true_and]
  have mem_qr (z) : z ∈ qr ↔ ∃ v, z = Sum.inr v ∧ Br.hostCluster v = i := by
    simp only [qr, Finset.mem_filter, Finset.mem_univ, true_and]
  have hL₀ : L₀.card = Fintype.card {x // B.sourceCluster x = i} := by
    dsimp only [L₀]
    rw [left_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter]
  have hQ₀ : Q₀.card = Fintype.card {v // B.hostCluster v = i} := by
    dsimp only [Q₀]
    rw [right_card, Fintype.card_subtype]
    congr 1
    ext v
    simp only [Finset.mem_filter]
  have hDL : DL ⊆ L₀ := by
    intro z hz
    obtain ⟨x, rfl, hx⟩ := (mem_left _ _).mp hz
    rw [mem_left]
    exact ⟨x, rfl, hx.2⟩
  have hDQ : DQ ⊆ Q₀ := by
    intro z hz
    obtain ⟨v, rfl, hv⟩ := (mem_right _ _).mp hz
    rw [mem_right]
    exact ⟨v, rfl, hv.2⟩
  have hE : E ⊆ L₀ \ DL := by
    intro z hz
    obtain ⟨x, rfl, hx⟩ := (mem_left _ _).mp hz
    simpa only [L₀, DL, Finset.mem_sdiff, mem_left, Sum.inl.injEq,
      exists_eq_left', hx.1, hx.2.2, false_and, not_false_eq_true, and_self]
  have hDLcard : (DL.card : ENNReal) ≤ L := by
    have heq : DL = (X.filter fun x => B.sourceCluster x = i).map
        Function.Embedding.inl := by
      ext z
      cases z <;> simp only [DL, mem_left, Finset.mem_map, Finset.mem_filter,
        Function.Embedding.inl_apply, Sum.inl.injEq, Sum.inr_ne_inl, false_and,
        exists_false, exists_eq_right, exists_eq_left', reduceCtorEq, and_false]
    simpa only [heq, Finset.card_map] using hX i
  have hDQcard : (DQ.card : ENNReal) ≤ L := by
    have heq : DQ = ((X.image f.toFun).filter fun v => B.hostCluster v = i).map
        Function.Embedding.inr := by
      ext z
      cases z <;> simp only [DQ, mem_right, Finset.mem_map, Finset.mem_filter,
        Function.Embedding.inr_apply, Sum.inr.injEq, Sum.inl_ne_inr, false_and,
        exists_false, exists_eq_right, exists_eq_left', reduceCtorEq, and_false]
    simpa only [heq, Finset.card_map] using himage i
  have hEcard : (E.card : ENNReal) ≤ J := by
    have heq : E = ((Finset.univ.filter fun x => x ∉ X ∧ ∃ y ∈ X, H.Adj x y).filter
        fun x => B.sourceCluster x = i).map Function.Embedding.inl := by
      ext z
      cases z <;> simp only [E, mem_left, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.Embedding.inl_apply, Sum.inl.injEq,
        Sum.inr_ne_inl, false_and, exists_false, exists_eq_right, exists_eq_left',
        reduceCtorEq, and_false]
      simp only [and_assoc]
    simpa only [heq, Finset.card_map] using hbuffer i
  have imageL : lr.map e = L₀ \ DL := by
    ext z
    cases z with
    | inl x =>
      simp only [Finset.mem_map, Finset.mem_sdiff]
      constructor
      · rintro ⟨z, hz, hzx⟩
        cases z with
        | inl a =>
          have ha : a.1 = x := Sum.inl.inj hzx
          subst x
          have hai : B.sourceCluster a.1 = i := by
            simpa only [mem_lr, Sum.inl.injEq, exists_eq_left', hsource] using hz
          simp only [L₀, DL, mem_left, Sum.inl.injEq, exists_eq_left']
          exact ⟨hai, fun h => a.2 h.1⟩
        | inr v => cases hzx
      · intro hx
        have hx' : B.sourceCluster x = i ∧ x ∉ X := by
          simp only [L₀, DL, mem_left, Sum.inl.injEq, exists_eq_left'] at hx
          exact ⟨hx.1, fun h => hx.2 ⟨h, hx.1⟩⟩
        refine ⟨Sum.inl ⟨x, hx'.2⟩, ?_, rfl⟩
        simp only [mem_lr, Sum.inl.injEq, exists_eq_left', hsource]
        exact hx'.1
    | inr v => simp [lr, L₀, DL, left, e]
  have imageQ : qr.map e = Q₀ \ DQ := by
    ext z
    cases z with
    | inr v =>
      simp only [Finset.mem_map, Finset.mem_sdiff]
      constructor
      · rintro ⟨z, hz, hzv⟩
        cases z with
        | inr a =>
          have ha : a.1 = v := Sum.inr.inj hzv
          subst v
          have hai : B.hostCluster a.1 = i := by
            simpa only [mem_qr, Sum.inr.injEq, exists_eq_left', hhost] using hz
          simp only [Q₀, DQ, mem_right, Sum.inr.injEq, exists_eq_left']
          exact ⟨hai, fun h => a.2 h.1⟩
        | inl x => cases hzv
      · intro hv
        have hv' : B.hostCluster v = i ∧ v ∉ X.image f.toFun := by
          simp only [Q₀, DQ, mem_right, Sum.inr.injEq, exists_eq_left'] at hv
          exact ⟨hv.1, fun h => hv.2 ⟨h, hv.1⟩⟩
        refine ⟨Sum.inr ⟨v, hv'.2⟩, ?_, rfl⟩
        simp only [mem_qr, Sum.inr.injEq, exists_eq_left', hhost]
        exact hv'.1
    | inl x => simp [qr, Q₀, DQ, right, e]
  have hlr : lr.card = m := by
    have heq : lr = (Finset.univ.filter fun x => Br.sourceCluster x = i).map
        Function.Embedding.inl := by
      ext z
      cases z <;> simp only [mem_lr, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.Embedding.inl_apply, Sum.inl.injEq,
        Sum.inr_ne_inl, false_and, exists_false, exists_eq_right, exists_eq_left',
        reduceCtorEq, and_false]
    rw [heq, Finset.card_map, ← Fintype.card_subtype]
    exact hleft i
  have hqr : qr.card = m := by
    have heq : qr = (Finset.univ.filter fun v => Br.hostCluster v = i).map
        Function.Embedding.inr := by
      ext z
      cases z <;> simp only [mem_qr, Finset.mem_map, Finset.mem_filter,
        Finset.mem_univ, true_and, Function.Embedding.inr_apply, Sum.inr.injEq,
        Sum.inl_ne_inr, false_and, exists_false, exists_eq_right, exists_eq_left',
        reduceCtorEq, and_false]
    rw [heq, Finset.card_map, ← Fintype.card_subtype]
    exact hright i
  have hL : (L₀ \ DL).card = m := by rw [← imageL, Finset.card_map, hlr]
  have hQ : (Q₀ \ DQ).card = m := by rw [← imageQ, Finset.card_map, hqr]
  have hRows : ∀ z ∈ (L₀ \ DL) \ E, ∀ w ∈ Q₀ \ DQ,
      g.Adj z w ↔ g₀.Adj z w := by
    intro z hz w hw
    obtain ⟨x, rfl, hxi⟩ := (mem_left _ _).mp
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).1
    obtain ⟨v, rfl, hvi⟩ := (mem_right _ _).mp (Finset.mem_sdiff.mp hw).1
    have hx : x ∉ X := by
      simpa only [DL, mem_left, Sum.inl.injEq, exists_eq_left', hxi, and_true] using
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hv : v ∉ X.image f.toFun := by
      simpa only [DQ, mem_right, Sum.inr.injEq, exists_eq_left', hvi, and_true] using
        (Finset.mem_sdiff.mp hw).2
    have hn : ¬ ∃ y ∈ X, H.Adj x y := by
      simpa only [E, mem_left, Sum.inl.injEq, exists_eq_left', hx, hxi, true_and,
        and_true, not_false_eq_true] using (Finset.mem_sdiff.mp hz).2
    rw [adj, adj₀]
    constructor
    · exact fun h => h.2.2.1
    · intro h
      exact ⟨hx, hv, h, fun y hy hxy => False.elim (hn ⟨y, hy, hxy⟩)⟩
  have exceptional : ∀ z ∈ E, (d' - ε') * ((Q₀ \ DQ).card : ENNReal) ≤
      (((Q₀ \ DQ).filter fun w => g.Adj z w).card : ENNReal) := by
    intro z hz
    obtain ⟨x, rfl, hx⟩ := (mem_left _ _).mp hz
    have candidates : ((Q₀ \ DQ).filter fun w => g.Adj (Sum.inl x) w) =
        (Finset.univ.filter fun v => Aup.allowed x v).map Function.Embedding.inr := by
      ext w
      cases w with
      | inl y => simp [Q₀, DQ, right]
      | inr v =>
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_map,
          Function.Embedding.inr_apply, Sum.inr.injEq, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hav⟩
          exact ⟨v, (adj x v).mp hav, rfl⟩
        · rintro ⟨v', hav, rfl⟩
          have hvi : B.hostCluster v' = i :=
            (Aup.cluster_respecting hav).symm.trans hx.2.2
          refine ⟨?_, (adj x v').mpr hav⟩
          simp only [Q₀, DQ, mem_right, Sum.inr.injEq, exists_eq_left']
          exact ⟨hvi, fun h => hav.2.1 h.1⟩
    have hncard : Set.ncard {v | Aup.allowed x v} =
        (Finset.univ.filter fun v => Aup.allowed x v).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext v
      simp
    rw [hQ, candidates, Finset.card_map]
    have hr : rho ≤ Set.ncard {v | Aup.allowed x v} := hreserve x hx.1 hx.2.1
    rw [hncard] at hr
    exact hrho.trans hr
  have hambient : LowerSuperRegularPair g (L₀ \ DL) (Q₀ \ DQ) ε' d' := by
    have original : LowerSuperRegularPair g₀ L₀ Q₀ ε d := by
      convert hSR i using 1
      · ext z
        cases z <;> simp [L₀, left]
      · ext z
        cases z <;> simp [Q₀, right]
    apply ExceptionalLeftLowerSuperRegular g₀ g L₀ Q₀ DL DQ E ε d ε' d' η
      hDL hDQ hE original hRows
    · rw [hL]
      exact hEcard.trans hJ
    · exact hε'
    · exact hε'top
    · rw [hL₀, hL, hEq i]
      exact hthreshold i
    · rw [hQ₀, hQ]
      exact hthreshold i
    · exact hdensity
    · rw [hQ, hQ₀]
      exact (hdegree i).trans (tsub_le_self.trans (tsub_le_tsub_left hDQcard _))
    · rw [hL, hL₀, hEq i]
      exact (hdegree i).trans
        ((tsub_le_tsub_right (tsub_le_tsub_left hDLcard _) J).trans
          (tsub_le_tsub_left hEcard _))
    · exact exceptional
  have neigh (T : Finset _) (v) :
      ((T.map e).filter fun w => g.Adj (e v) w).card =
        (T.filter fun w => gr.Adj v w).card := by
    rw [Finset.filter_map]
    rw [Finset.card_map]
    congr 1
    ext w
    simp only [Finset.mem_filter, Function.comp_apply, ← reflect]
  have neigh' (T : Finset _) (w) :
      ((T.map e).filter fun v => g.Adj v (e w)).card =
        (T.filter fun v => gr.Adj v w).card := by
    rw [Finset.filter_map]
    rw [Finset.card_map]
    congr 1
    ext v
    simp only [Finset.mem_filter, Function.comp_apply, ← reflect]
  have density (P Q : Finset _) :
      PairDensity g (P.map e) (Q.map e) = PairDensity gr P Q := by
    unfold PairDensity
    simp only [Finset.product_eq_sprod]
    rw [← Finset.prodMap_map_product, Finset.filter_map]
    simp only [Finset.card_map]
    congr 2
    congr 1
    ext p
    simp only [Finset.mem_filter, Function.comp_apply]
    change (_ ∧ g.Adj (e p.1) (e p.2)) ↔ (_ ∧ gr.Adj p.1 p.2)
    rw [reflect]
  rw [← imageL, ← imageQ] at hambient
  change LowerSuperRegularPair gr lr qr ε' d'
  refine ⟨?_, ?_, ?_⟩
  · intro P hP Q hQ hPt hQt
    rw [← density]
    apply hambient.1 (P.map e) (Finset.map_subset_map.mpr hP)
      (Q.map e) (Finset.map_subset_map.mpr hQ)
    · simpa only [Finset.card_map] using hPt
    · simpa only [Finset.card_map] using hQt
  · intro v hv
    have hv' : e v ∈ lr.map e := Finset.mem_map.mpr ⟨v, hv, rfl⟩
    simpa only [Finset.card_map, neigh] using hambient.2.1 (e v) hv'
  · intro w hw
    have hw' : e w ∈ qr.map e := Finset.mem_map.mpr ⟨w, hw, rfl⟩
    simpa only [Finset.card_map, neigh'] using hambient.2.2 (e w) hw'
