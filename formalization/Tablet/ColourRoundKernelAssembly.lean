import Tablet.ColourRoundInvariant
import Tablet.ColourRoundUntouchedGeometry
import Tablet.ExtendUpdatedPartialEmbedding
import Tablet.UpdatedCandidacyNonneighborExtension
import Tablet.VertexSpreadRestriction

-- [TABLET NODE: ColourRoundKernelAssembly]
theorem ColourRoundKernelAssembly
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (epsilon density : ℕ → ENNReal)
    (D : ℕ) (C : ENNReal) (n round : ℕ) (touched : Finset (Fin r))
    (X : Finset VH) (mu : PMF (PartialCompatibleEmbedding B A X))
    (hinv : ColourRoundInvariant B A colour epsilon density D C n round touched X mu)
    (i : Fin r) (hi : (colour i).val = round) (hiS : i ∉ touched) :
    let X' := Finset.univ.filter fun x : VH =>
      (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ insert i touched
    let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
    (∀ f ∈ mu.support,
      ∃ nu : PMF (PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y),
        VertexSpreadOn (nu.map fun g => fun y : Y => g.toFun y.1) (C / n) Set.univ ∧
        (∀ g ∈ nu.support, ∀ h : PartialCompatibleEmbedding B A X',
          (∀ x ∈ X, h.toFun x = f.toFun x) →
          (∀ y ∈ Y, h.toFun y = g.toFun y) →
          ∀ j : Fin r, R.Adj i j → j ∉ touched → round ≤ (colour j).val →
            let exposure := (Finset.univ.filter fun k : Fin r =>
              ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
            let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
              ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X'
            let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
              ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧ v ∉ X'.image h.toFun
            let Aj : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
              ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
                (y, v) ∈ UpdatedCandidacyCluster B A X' h j
            ∃ W : SimpleGraph (VH ⊕ VG), W ≤ Aj ∧
              @SuperRegularPair (VH ⊕ VG) _ W (Classical.decRel _)
                L Q (epsilon (round + 1)) (density (exposure + 1)))) →
    ∃ kappa : PartialCompatibleEmbedding B A X → PMF (PartialCompatibleEmbedding B A X'),
      (∀ f ∈ mu.support, ∀ h ∈ (kappa f).support, ∀ x ∈ X,
        h.toFun x = f.toFun x) ∧
      (∀ f ∈ mu.support, VertexSpreadOn
        ((kappa f).map fun h => fun y : Y => h.toFun y.1) (C / n) Set.univ) ∧
      ColourRoundInvariant B A colour epsilon density D C n round
        (insert i touched) X' (mu.bind kappa) := by
-- BODY
  classical
  dsimp only
  intro hlocal
  let X' := Finset.univ.filter fun x : VH =>
    (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ insert i touched
  let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
  rcases hinv with ⟨hround, hdegree, hcolour, hS, hX, hspread, hwitness⟩
  have hgeom := ColourRoundUntouchedGeometry R colour D round touched i hdegree hcolour hS hi hiS
  have hdom : X' = X ∪ Y := by
    rw [hX]
    ext x
    simp only [X', Y, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_insert]
    tauto
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hc : B.sourceCluster x = i := (Finset.mem_filter.mp hy).2
    rw [hX] at hx
    have hh := (Finset.mem_filter.mp hx).2
    rw [hc, hi] at hh
    exact hh.elim (fun h => (Nat.lt_irrefl _ h)) hiS
  have hExt (f : PartialCompatibleEmbedding B A X)
      (g : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y) :
      ∃ h : PartialCompatibleEmbedding B A X',
        (∀ x ∈ X, h.toFun x = f.toFun x) ∧ (∀ y ∈ Y, h.toFun y = g.toFun y) := by
    rw [hdom]
    exact ExtendUpdatedPartialEmbedding B A X Y hXY f g
  let ext (f : PartialCompatibleEmbedding B A X)
      (g : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y) := (hExt f g).choose
  have extX (f : PartialCompatibleEmbedding B A X)
      (g : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y) :=
    (hExt f g).choose_spec.1
  have extY (f : PartialCompatibleEmbedding B A X)
      (g : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y) :=
    (hExt f g).choose_spec.2
  let nu (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) := (hlocal f hf).choose
  have hnu (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) :=
    (hlocal f hf).choose_spec
  let K (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) := (nu f hf).map (ext f)
  obtain ⟨f0, hf0⟩ := mu.support_nonempty
  let kappa : PartialCompatibleEmbedding B A X → PMF (PartialCompatibleEmbedding B A X') :=
    fun f => if hf : f ∈ mu.support then K f hf else K f0 hf0
  have hk (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) : kappa f = K f hf := by
    simp only [kappa, dif_pos hf]
  have hkernelX : ∀ f ∈ mu.support, ∀ h ∈ (kappa f).support,
      ∀ x ∈ X, h.toFun x = f.toFun x := by
    intro f hf h hh
    rw [hk f hf] at hh
    obtain ⟨g, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    exact extX f g
  have hkernelY : ∀ f ∈ mu.support, VertexSpreadOn
      ((kappa f).map fun h => fun y : Y => h.toFun y.1) (C / n) Set.univ := by
    intro f hf
    rw [hk f hf, PMF.map_comp]
    have heq : (fun h : PartialCompatibleEmbedding B A X' => fun y : Y => h.toFun y.1) ∘
        ext f = (fun g => fun y : Y => g.toFun y.1) := by
      funext g y
      exact extY f g y.1 y.2
    rw [heq]
    exact (hnu f hf).1
  have hun (j : Fin r) (hj : j ∉ insert i touched) (hc : round ≤ (colour j).val) :
      ∀ y, B.sourceCluster y = j → y ∉ X' := by
    intro y hy hmem
    have hh := (Finset.mem_filter.mp hmem).2
    rw [hy] at hh
    exact hh.elim (fun h => (not_lt_of_ge hc h)) hj
  let out : PartialCompatibleEmbedding B A X' → X ⊕ Y → VG :=
    fun h => Sum.elim (fun x : X => h.toFun x.1) (fun y : Y => h.toFun y.1)
  have hcombined : VertexSpreadOn ((mu.bind kappa).map out) (C / n) Set.univ := by
    let old := fun f : PartialCompatibleEmbedding B A X => fun x : X => f.toFun x.1
    let new := fun h : PartialCompatibleEmbedding B A X' => fun y : Y => h.toFun y.1
    have hagree (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support)
        (h : PartialCompatibleEmbedding B A X') (hh : h ∈ (kappa f).support) :
        out h = Sum.elim (old f) (new h) := by
      funext z
      cases z with
      | inl x => exact hkernelX f hf h hh x.1 x.2
      | inr y => rfl
    classical
    refine ⟨hspread.1, ?_⟩
    intro s x y hx _
    let L := {i : Fin s // ∃ u : X, x i = Sum.inl u}
    let R := {i : Fin s // ¬∃ u : X, x i = Sum.inl u}
    let left : L → X := fun i => Classical.choose i.property
    have hleft (i : L) : x i.val = Sum.inl (left i) :=
      Classical.choose_spec i.property
    have rexists (i : R) : ∃ u : Y, x i.val = Sum.inr u := by
      cases hi : x i.val with
      | inl u => exact False.elim (i.property ⟨u, hi⟩)
      | inr u => exact ⟨u, rfl⟩
    let right : R → Y := fun i => Classical.choose (rexists i)
    have hright (i : R) : x i.val = Sum.inr (right i) := Classical.choose_spec (rexists i)
    have linj : Function.Injective left := by
      intro i j hij
      apply Subtype.ext
      apply hx
      rw [hleft i, hleft j, hij]
    have rinj : Function.Injective right := by
      intro i j hij
      apply Subtype.ext
      apply hx
      rw [hright i, hright j, hij]
    let a := Fintype.card L
    let b := Fintype.card R
    have hab : a + b = s := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using
        Fintype.card_congr (Equiv.sumCompl (fun i : Fin s => ∃ u : X, x i = Sum.inl u))
    let eL := Fintype.equivFin L
    let eR := Fintype.equivFin R
    let EL : Set (X → VG) := {f | ∀ i : L, f (left i) = y i.val}
    let ER : Set (Y → VG) := {g | ∀ i : R, g (right i) = y i.val}
    have hEL : (mu.map old).toOuterMeasure EL ≤ (C / n) ^ a := by
      have heq : CylinderEvent (fun j : Fin a => left (eL.symm j))
          (fun j => y (eL.symm j).val) = EL := by
        ext f
        constructor
        · intro h i
          simpa only [Equiv.symm_apply_apply] using h (eL i)
        · intro h j
          exact h (eL.symm j)
      rw [← heq]
      exact hspread.2 a _ _ (linj.comp eL.symm.injective) (fun _ => Set.mem_univ _)
    have hER (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) :
        ((kappa f).map new).toOuterMeasure ER ≤ (C / n) ^ b := by
      have heq : CylinderEvent (fun j : Fin b => right (eR.symm j))
          (fun j => y (eR.symm j).val) = ER := by
        ext g
        constructor
        · intro h i
          simpa only [Equiv.symm_apply_apply] using h (eR i)
        · intro h j
          exact h (eR.symm j)
      rw [← heq]
      exact (hkernelY f hf).2 b _ _ (rinj.comp eR.symm.injective) (fun _ => Set.mem_univ _)
    have joint (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) (h : PartialCompatibleEmbedding B A X') (hh : h ∈ (kappa f).support) :
        out h ∈ CylinderEvent x y ↔ old f ∈ EL ∧ new h ∈ ER := by
      rw [hagree f hf h hh]
      change (∀ i, Sum.elim (old f) (new h) (x i) = y i) ↔
        (∀ i : L, old f (left i) = y i.val) ∧ (∀ i : R, new h (right i) = y i.val)
      constructor
      · intro h
        exact ⟨fun i => by simpa only [hleft i, Sum.elim_inl] using h i.val,
          fun i => by simpa only [hright i, Sum.elim_inr] using h i.val⟩
      · rintro ⟨hl, hr⟩ i
        by_cases hi : ∃ u : X, x i = Sum.inl u
        · rw [hleft ⟨i, hi⟩]
          exact hl ⟨i, hi⟩
        · rw [hright ⟨i, hi⟩]
          exact hr ⟨i, hi⟩
    have cond (f : PartialCompatibleEmbedding B A X) (hf : f ∈ mu.support) :
        ((kappa f).map out).toOuterMeasure (CylinderEvent x y) ≤
          if old f ∈ EL then (C / n) ^ b else 0 := by
      rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
      have heq : (∑' h, ((out ⁻¹' CylinderEvent x y).indicator (kappa f)) h) =
          if old f ∈ EL then ((kappa f).map new).toOuterMeasure ER else 0 := by
        rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
        by_cases ho : old f ∈ EL
        · simp only [ho, if_true]
          apply tsum_congr
          intro h
          by_cases hh : h ∈ (kappa f).support
          · simp only [Set.indicator_apply, Set.mem_preimage]
            rw [joint f hf h hh]
            simp only [ho, true_and]
          · have hz : kappa f h = 0 := by simpa only [PMF.mem_support_iff, not_not] using hh
            simp [Set.indicator_apply, hz]
        · simp only [ho, if_false]
          apply ENNReal.tsum_eq_zero.mpr
          intro h
          by_cases hh : h ∈ (kappa f).support
          · have hn : out h ∉ CylinderEvent x y := fun hp => ho ((joint f hf h hh).mp hp).1
            simp [hn]
          · have hz : kappa f h = 0 := by simpa only [PMF.mem_support_iff, not_not] using hh
            simp [hz]
      rw [heq]
      by_cases ho : old f ∈ EL
      · simpa only [ho, if_true] using hER f hf
      · simp only [ho, if_false, le_refl]
    calc
      ((mu.bind kappa).map out).toOuterMeasure (CylinderEvent x y) =
          ∑' f, mu f * ((kappa f).map out).toOuterMeasure (CylinderEvent x y) := by
        rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_bind_apply]
        apply tsum_congr
        intro f
        rw [PMF.toOuterMeasure_map_apply]
      _ ≤ ∑' f, (if old f ∈ EL then mu f else 0) * (C / n) ^ b := by
        apply ENNReal.tsum_le_tsum
        intro f
        by_cases hf : f ∈ mu.support
        · have h := mul_le_mul_right (cond f hf) (mu f)
          by_cases ho : old f ∈ EL <;> simpa only [ho, if_true, if_false, mul_zero, zero_mul] using h
        · have hz : mu f = 0 := by simpa only [PMF.mem_support_iff, not_not] using hf
          simp [hz]
      _ = (mu.map old).toOuterMeasure EL * (C / n) ^ b := by
        rw [ENNReal.tsum_mul_right, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
        simp only [Set.indicator_apply, Set.mem_preimage]
      _ ≤ (C / n) ^ a * (C / n) ^ b := mul_le_mul_left hEL _
      _ = (C / n) ^ s := by rw [← pow_add, hab]
  let e : X' → X ⊕ Y := fun x =>
    if hx : x.1 ∈ X then Sum.inl ⟨x.1, hx⟩ else
      Sum.inr ⟨x.1, (Finset.mem_union.mp (hdom ▸ x.2)).resolve_left hx⟩
  have heval (x : X') : Sum.elim (Subtype.val : X → VH) (Subtype.val : Y → VH) (e x) = x.1 := by
    dsimp only [e]
    split <;> rfl
  have heinj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    rw [← heval x, ← heval y, hxy]
  have hfullspread : VertexSpreadOn
      ((mu.bind kappa).map fun h => fun x : X' => h.toFun x.1) (C / n) Set.univ := by
    have hr := VertexSpreadRestriction (U := Set.univ) ⟨e, heinj⟩ hcombined
    change VertexSpreadOn (((mu.bind kappa).map out).map (fun f => f ∘ e))
      (C / n) Set.univ at hr
    rw [PMF.map_comp] at hr
    have heq : (fun f : X ⊕ Y → VG => f ∘ e) ∘ out =
        (fun h : PartialCompatibleEmbedding B A X' => fun x : X' => h.toFun x.1) := by
      funext h x
      dsimp only [Function.comp_def, out, e]
      split <;> rfl
    rwa [heq] at hr
  refine ⟨kappa, hkernelX, hkernelY, hround, hdegree, hcolour, ?_, rfl, hfullspread, ?_⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact hS j hj
  · intro h hh j hj hc
    obtain ⟨f, hf, hh⟩ := (PMF.mem_support_bind_iff _ _ _).mp hh
    have hjS : j ∉ touched := fun h => hj (Finset.mem_insert_of_mem h)
    have hji : j ≠ i := fun h => hj (h.symm ▸ Finset.mem_insert_self i touched)
    obtain ⟨hexp, _, Wold, hWold, hsuperOld⟩ := hwitness f hf j hjS hc
    have hcount := hgeom.2.2.1 j
    by_cases hadj : R.Adj i j
    · have hchange := hgeom.2.2.2 j hadj
      have htouchedNew : ((insert i touched).filter fun k => R.Adj j k).Nonempty :=
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, R.symm hadj⟩⟩
      dsimp only
      rw [hchange.2, if_pos htouchedNew]
      refine ⟨by omega, hcount, ?_⟩
      rw [hk f hf] at hh
      obtain ⟨g, hg, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
      exact (hnu f hf).2 g hg (ext f g) (extX f g) (extY f g) j hadj hjS hc
    · have hnji : ¬R.Adj j i := fun h => hadj (R.symm h)
      have hE : (Finset.univ.filter fun k : Fin r =>
          ((colour k).val < round ∨ k ∈ insert i touched) ∧ R.Adj j k) =
          (Finset.univ.filter fun k : Fin r =>
          ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k) := by
        ext k
        by_cases hki : k = i
        · subst k
          simp [hnji]
        · simp [Finset.mem_insert, hki]
      have hT : ((insert i touched).filter fun k => R.Adj j k) =
          (touched.filter fun k => R.Adj j k) := by
        simp [Finset.filter_insert, hnji]
      have hpersist := UpdatedCandidacyNonneighborExtension B A X Y X' f h i j hdom
        (fun y hy => (Finset.mem_filter.mp hy).2) (hun j hj hc) hnji hji
        (hkernelX f hf h hh)
      dsimp only
      rw [hE, hT]
      refine ⟨hexp, by simpa only [hT] using hcount, Wold, ?_, ?_⟩
      · change Wold ≤ SimpleGraph.fromRel (fun p s =>
          ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
            (y, v) ∈ UpdatedCandidacyCluster B A X' h j)
        rw [hpersist.1]
        exact hWold
      · have hL : (Finset.univ.filter fun z : VH ⊕ VG =>
            ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X') =
            (Finset.univ.filter fun z : VH ⊕ VG =>
            ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X) := by
          apply Finset.filter_congr
          intro z _
          constructor <;> rintro ⟨y, hz, hy, hm⟩
          · exact ⟨y, hz, hy, (hpersist.2.1 y hy).mp hm⟩
          · exact ⟨y, hz, hy, (hpersist.2.1 y hy).mpr hm⟩
        have hQ : (Finset.univ.filter fun z : VH ⊕ VG =>
            ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧ v ∉ X'.image h.toFun) =
            (Finset.univ.filter fun z : VH ⊕ VG =>
            ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧ v ∉ X.image f.toFun) := by
          apply Finset.filter_congr
          intro z _
          constructor <;> rintro ⟨v, hz, hv, hm⟩
          · exact ⟨v, hz, hv, (hpersist.2.2 v hv).mp hm⟩
          · exact ⟨v, hz, hv, (hpersist.2.2 v hv).mpr hm⟩
        rw [hL, hQ]
        exact hsuperOld
