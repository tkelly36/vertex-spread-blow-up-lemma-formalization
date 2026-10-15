import Tablet.BlowUpInstance

-- [TABLET NODE: EquitableSquareColoring]
theorem EquitableSquareColoring :
    ∀ (Delta r n : ℕ), 1 ≤ Delta →
      ∀ {VH VG : Type*} [Fintype VH] [Fintype VG] [DecidableEq VH]
        {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
        [DecidableRel H.Adj] (B : BlowUpInstance r VH VG H G R),
        H.maxDegree ≤ Delta →
        (∀ i, (Finset.univ.filter fun x : VH => B.sourceCluster x = i).card = n) →
        ∃ color : VH → Fin (Delta ^ 2),
          (∀ i j,
            let s := Finset.univ.filter fun x : VH =>
              B.sourceCluster x = i ∧ color x = j
            s.card = n / (Delta ^ 2) ∨ s.card = n / (Delta ^ 2) + 1) ∧
          ∀ {x y}, B.sourceCluster x = B.sourceCluster y → color x = color y →
            x ≠ y → ¬ H.Adj x y ∧ ¬ ∃ z, H.Adj x z ∧ H.Adj y z := by
-- BODY
  classical
  intro Delta r n hDelta VH VG _ _ _ H G R _ B hmax hcluster
  let X : Fin r -> Type _ := fun i => {x : VH // B.sourceCluster x = i}
  let Q : (i : Fin r) -> SimpleGraph (X i) := fun i =>
    SimpleGraph.fromRel fun x y => exists z : VH, H.Adj x.1 z ∧ H.Adj y.1 z
  have hdegH (x : VH) : H.degree x ≤ Delta :=
    (H.degree_le_maxDegree x).trans hmax
  have hdegQ (i : Fin r) (x : X i) : (Q i).degree x ≤ Delta ^ 2 - 1 := by
    rw [Nat.le_sub_one_iff_lt (by positivity)]
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    by_cases hx : Nonempty ((Q i).neighborSet x)
    · have hcommon (y : (Q i).neighborSet x) :
          exists z : VH, H.Adj x.1 z ∧ H.Adj y.1.1 z := by
        have hy : (Q i).Adj x y.1 := y.2
        exact ((SimpleGraph.fromRel_adj _ _ _).mp hy).2.elim id fun h =>
          ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩
      let chooseZ : (Q i).neighborSet x -> VH := fun y => Classical.choose (hcommon y)
      have hchooseZ (y : (Q i).neighborSet x) :
          H.Adj x.1 (chooseZ y) ∧ H.Adj y.1.1 (chooseZ y) := by
        exact Classical.choose_spec (hcommon y)
      let f : (Q i).neighborSet x ->
          Sigma fun z : H.neighborSet x.1 => H.neighborSet z.1 := fun y =>
        ⟨⟨chooseZ y, (hchooseZ y).1⟩, ⟨y.1.1, H.symm (hchooseZ y).2⟩⟩
      have hf : Function.Injective f := by
        intro y y' hy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun p => p.2.1) hy
      have hnot : ¬ Function.Surjective f := by
        intro hsurj
        let y : (Q i).neighborSet x := Classical.choice hx
        let z : H.neighborSet x.1 := ⟨chooseZ y, (hchooseZ y).1⟩
        obtain ⟨w, hw⟩ := hsurj ⟨z, ⟨x.1, H.symm z.2⟩⟩
        have hwx : w.1 = x := by
          apply Subtype.ext
          exact congrArg (fun p => p.2.1) hw
        have hwadj := w.2
        rw [hwx] at hwadj
        exact (Q i).loopless.irrefl x hwadj
      calc
        Fintype.card ((Q i).neighborSet x) <
            Fintype.card (Sigma fun z : H.neighborSet x.1 => H.neighborSet z.1) :=
          Fintype.card_lt_of_injective_not_surjective f hf hnot
        _ = ∑ z : H.neighborSet x.1, H.degree z.1 := by
          rw [Fintype.card_sigma]
          congr 1
          funext z
          exact SimpleGraph.card_neighborSet_eq_degree H z.1
        _ ≤ ∑ _z : H.neighborSet x.1, Delta := by
          exact Finset.sum_le_sum fun z _ => hdegH z.1
        _ = H.degree x.1 * Delta := by
          rw [Finset.sum_const, Finset.card_univ,
            SimpleGraph.card_neighborSet_eq_degree]
          simp
        _ ≤ Delta * Delta := Nat.mul_le_mul_right Delta (hdegH x.1)
        _ = Delta ^ 2 := by ring
    · simp only [not_nonempty_iff] at hx
      have hpos : 0 < Delta := by omega
      simp [pow_pos hpos]
  have hcolor : ∀ i : Fin r,
      ∃ c : X i -> Fin (Delta ^ 2),
        (∀ ⦃v w⦄, (Q i).Adj v w → c v ≠ c w) ∧
          ∀ a b, Fintype.card {v : X i // c v = a} ≤
              Fintype.card {v : X i // c v = b} + 1 ∧
            Fintype.card {v : X i // c v = b} ≤
              Fintype.card {v : X i // c v = a} + 1 := by
    intro i
    let e := Fintype.equivFin (X i)
    let K : SimpleGraph (Fin (Fintype.card (X i))) := SimpleGraph.comap e.symm (Q i)
    have hdegK (v : Fin (Fintype.card (X i))) : K.degree v ≤ Delta ^ 2 - 1 := by
      let en : K.neighborSet v ≃ (Q i).neighborSet (e.symm v) :=
        { toFun := fun w => ⟨e.symm w.1, by
            have hw := w.2
            change K.Adj v w.1 at hw
            change (Q i).Adj (e.symm v) (e.symm w.1)
            simpa [K] using hw⟩
          invFun := fun w => ⟨e w.1, by
            have hw := w.2
            change (Q i).Adj (e.symm v) w.1 at hw
            change K.Adj v (e w.1)
            simpa [K] using hw⟩
          left_inv := by intro w; apply Subtype.ext; simp
          right_inv := by intro w; apply Subtype.ext; simp }
      rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr en,
        SimpleGraph.card_neighborSet_eq_degree]
      exact hdegQ i (e.symm v)
    by_cases hDone : Delta = 1
    · subst Delta
      refine ⟨fun _ => 0, ?_⟩
      constructor
      · intro v w hvw
        have hpos : 0 < (Q i).degree v := ((Q i).degree_pos_iff_exists_adj v).2 ⟨w, hvw⟩
        have := hdegQ i v
        simp at this
        omega
      · intro a b
        fin_cases a
        fin_cases b
        omega
    · have htwo : 2 ≤ Delta := by omega
      have hsq : 1 < Delta ^ 2 := by nlinarith
      obtain ⟨ck, hck⟩ := HajnalSzemerediFormalization.HajnalSzemeredi K
        (r := Delta ^ 2 - 1) (by omega) hdegK
      let ci : X i -> Fin (Delta ^ 2) := fun x =>
        Fin.cast (Nat.sub_add_cancel (show 1 ≤ Delta ^ 2 by omega)) (ck (e x))
      refine ⟨ci, ?_, ?_⟩
      · intro x y hxy hs
        have hkadj : K.Adj (e x) (e y) := by simpa [K] using hxy
        have hkne := hck.1 hkadj
        apply hkne
        exact (Fin.cast_injective _ hs)
      · intro a b
        have hcard (k : Fin (Delta ^ 2)) :
            Fintype.card {x : X i // ci x = k} =
              Fintype.card {v : Fin (Fintype.card (X i)) //
                ck v = Fin.cast (Nat.sub_add_cancel (show 1 ≤ Delta ^ 2 by omega)).symm k} := by
          apply Fintype.card_congr
          exact
            { toFun := fun x => ⟨e x.1, by
                apply Fin.cast_injective (Nat.sub_add_cancel (show 1 ≤ Delta ^ 2 by omega))
                simpa [ci] using x.2⟩
              invFun := fun v => ⟨e.symm v.1, by
                have := congrArg
                  (Fin.cast (Nat.sub_add_cancel (show 1 ≤ Delta ^ 2 by omega))) v.2
                simpa [ci] using this⟩
              left_inv := by intro x; apply Subtype.ext; simp
              right_inv := by intro v; apply Subtype.ext; simp }
        rw [hcard a, hcard b]
        exact hck.2 _ _
  let c : (i : Fin r) -> X i -> Fin (Delta ^ 2) := fun i =>
    Classical.choose (hcolor i)
  let color : VH -> Fin (Delta ^ 2) := fun x => c (B.sourceCluster x) ⟨x, rfl⟩
  have color_eq (x : VH) (i : Fin r) (hx : B.sourceCluster x = i) :
      color x = c i ⟨x, hx⟩ := by
    subst i
    rfl
  refine ⟨color, ?_, ?_⟩
  · intro i j
    let fiberCard : Fin (Delta ^ 2) -> ℕ := fun k =>
      Fintype.card {x : X i // c i x = k}
    have hsum : ∑ k, fiberCard k = n := by
      rw [show n = Fintype.card (X i) by
        simpa [X, Fintype.card_subtype] using (hcluster i).symm]
      simpa [fiberCard, Fintype.card_subtype] using
        (Finset.card_eq_sum_card_fiberwise (s := Finset.univ)
          (f := c i) (t := Finset.univ) (by simp)).symm
    have hbal : ∀ a b, fiberCard a ≤ fiberCard b + 1 ∧
        fiberCard b ≤ fiberCard a + 1 := by
      simpa [fiberCard, c] using (Classical.choose_spec (hcolor i)).2
    have hj : fiberCard j = n / (Delta ^ 2) ∨
        fiberCard j = n / (Delta ^ 2) + 1 := by
      have hk : Fintype.card (Fin (Delta ^ 2)) = Delta ^ 2 := Fintype.card_fin _
      have hpos : 0 < Delta ^ 2 := by positivity
      have hlower : n / (Delta ^ 2) ≤ fiberCard j := by
        by_contra h
        have hall : ∀ k, fiberCard k ≤ n / (Delta ^ 2) := by
          intro k
          have := (hbal k j).1
          omega
        have hstrict : (∑ k, fiberCard k) < ∑ _k : Fin (Delta ^ 2), n / (Delta ^ 2) := by
          refine Finset.sum_lt_sum (s := Finset.univ) (fun k _ => hall k) ?_
          exact ⟨j, Finset.mem_univ _, by omega⟩
        simp only [Finset.sum_const, Finset.card_univ, hk, Nat.nsmul_eq_mul] at hstrict
        have hle := Nat.mul_div_le n (Delta ^ 2)
        omega
      have hupper : fiberCard j ≤ n / (Delta ^ 2) + 1 := by
        by_contra h
        have hall : ∀ k, n / (Delta ^ 2) + 1 ≤ fiberCard k := by
          intro k
          have := (hbal j k).1
          omega
        have hstrict : (∑ _k : Fin (Delta ^ 2), (n / (Delta ^ 2) + 1)) <
            ∑ k, fiberCard k := by
          refine Finset.sum_lt_sum (s := Finset.univ) (fun k _ => hall k) ?_
          exact ⟨j, Finset.mem_univ _, by omega⟩
        simp only [Finset.sum_const, Finset.card_univ, hk, Nat.nsmul_eq_mul] at hstrict
        have hlt := Nat.lt_mul_div_succ n hpos
        omega
      omega
    have heq :
        (Finset.univ.filter fun x : VH => B.sourceCluster x = i ∧ color x = j).card =
          fiberCard j := by
      let e : {x : VH // B.sourceCluster x = i ∧ color x = j} ≃
          {x : X i // c i x = j} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            rw [← color_eq x.1 i x.2.1]
            exact x.2.2⟩
          invFun := fun x => ⟨x.1.1, x.1.2, by
            rw [color_eq x.1.1 i x.1.2]
            exact x.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr e
    simpa [heq] using hj
  · intro x y hxy hsame hne
    have hq : (Q (B.sourceCluster x)).Adj ⟨x, rfl⟩ ⟨y, hxy.symm⟩ -> False := by
      intro hadj
      apply (Classical.choose_spec (hcolor (B.sourceCluster x))).1 hadj
      change c (B.sourceCluster x) ⟨x, rfl⟩ =
        c (B.sourceCluster x) ⟨y, hxy.symm⟩
      rw [← color_eq x (B.sourceCluster x) rfl,
        ← color_eq y (B.sourceCluster x) hxy.symm]
      exact hsame
    constructor
    · intro hadj
      have hr := B.reduced_support hadj
      rw [hxy] at hr
      exact R.loopless.irrefl (B.sourceCluster y) hr
    · rintro ⟨z, hxz, hyz⟩
      exact hq ((SimpleGraph.fromRel_adj _ _ _).2
        ⟨by
          intro he
          apply hne
          exact congrArg Subtype.val he,
          Or.inl ⟨z, hxz, hyz⟩⟩)
