import Tablet.ColourRoundInvariant
import Tablet.PerfectMatching

-- [TABLET NODE: ColourRoundMatchingRecords]
theorem ColourRoundMatchingRecords
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (round : ℕ) (touched : Finset (Fin r))
    (X : Finset VH) (f : PartialCompatibleEmbedding B A X)
    (i : Fin r) (hi : (colour i).val = round) (hiS : i ∉ touched)
    (hX : X = Finset.univ.filter fun x =>
      (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ touched)
    (hY : (Finset.univ.filter fun x : VH => B.sourceCluster x = i).Nonempty) :
    let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
    let K0 := Finset.univ.filter fun v : VG => B.hostCluster v = i
    let U := Y.image (Sum.inl : VH → VH ⊕ VG)
    let K := K0.image (Sum.inr : VG → VH ⊕ VG)
    let X' := Finset.univ.filter fun x : VH =>
      (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ insert i touched
    let Ai := SimpleGraph.fromRel fun p s =>
      ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
        (y, v) ∈ UpdatedCandidacyCluster B A X f i
    ∀ (F : SimpleGraph (VH ⊕ VG)) (hUK : Disjoint U K), F ≤ Ai →
      Nonempty {sigma : U → K // PerfectMatching F U K hUK sigma} →
      ∃ (e : Y ≃ U) (v : K ↪ VG)
        (lift : {sigma : U → K // PerfectMatching F U K hUK sigma} ↪
          PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y),
        (∀ y : Y, (e y : VH ⊕ VG) = Sum.inl y.1) ∧
        (∀ k : K, Sum.inr (v k) = (k : VH ⊕ VG)) ∧
        (∀ sigma, ∀ y : Y, (lift sigma).toFun y.1 = v (sigma.val (e y))) ∧
        (∀ sigma, ∀ h : PartialCompatibleEmbedding B A X',
          (∀ x ∈ X, h.toFun x = f.toFun x) →
          (∀ y ∈ Y, h.toFun y = (lift sigma).toFun y) →
          ∀ j : Fin r, R.Adj i j → j ∉ touched → round ≤ (colour j).val →
            let Vj := (Finset.univ.filter fun y : VH => B.sourceCluster y = j).image
              (Sum.inl : VH → VH ⊕ VG)
            let Zj := (Finset.univ.filter fun w : VG => B.hostCluster w = j).image
              (Sum.inr : VG → VH ⊕ VG)
            let T := SimpleGraph.fromRel fun p s =>
              ∃ y : VH, ∃ w : VG, p = Sum.inl y ∧ s = Sum.inr w ∧
                (y, w) ∈ UpdatedCandidacyCluster B A X f j ∧
                ∀ u : U, (∃ x : VH, (u : VH ⊕ VG) = Sum.inl x ∧ H.Adj x y) →
                  ∃ z : VG, (sigma.val u : VH ⊕ VG) = Sum.inr z ∧ G.Adj z w
            let Aj := SimpleGraph.fromRel fun p s =>
              ∃ y : VH, ∃ w : VG, p = Sum.inl y ∧ s = Sum.inr w ∧
                (y, w) ∈ UpdatedCandidacyCluster B A X' h j
            T ≤ Aj ∧
            (Finset.univ.filter fun z : VH ⊕ VG =>
              ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X') = Vj ∧
            (Finset.univ.filter fun z : VH ⊕ VG =>
              ∃ w : VG, z = Sum.inr w ∧ B.hostCluster w = j ∧
                w ∉ X'.image h.toFun) = Zj) := by
-- BODY
  classical
  dsimp only
  intro F hUK hFA hmatch
  let Y := Finset.univ.filter fun x : VH => B.sourceCluster x = i
  let K0 := Finset.univ.filter fun w : VG => B.hostCluster w = i
  let U := Y.image (Sum.inl : VH → VH ⊕ VG)
  let K := K0.image (Sum.inr : VG → VH ⊕ VG)
  let X' := Finset.univ.filter fun x : VH =>
    (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ insert i touched
  let ein : Y → U := fun y => ⟨Sum.inl y.1, Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩⟩
  have hein : Function.Bijective ein := by
    constructor
    · intro a b hab
      exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hab))
    · intro u
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp u.2
      exact ⟨⟨y, hy⟩, Subtype.ext heq⟩
  let e : Y ≃ U := Equiv.ofBijective ein hein
  have he (y : Y) : (e y : VH ⊕ VG) = Sum.inl y.1 := rfl
  have hk (k : K) : ∃ w : VG, Sum.inr w = (k : VH ⊕ VG) := by
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp k.2
    exact ⟨w, hw⟩
  let v : K ↪ VG :=
    { toFun := fun k => Classical.choose (hk k)
      inj' := by
        intro a b hab
        apply Subtype.ext
        calc
          (a : VH ⊕ VG) = Sum.inr (Classical.choose (hk a)) := (Classical.choose_spec (hk a)).symm
          _ = Sum.inr (Classical.choose (hk b)) := congrArg Sum.inr hab
          _ = (b : VH ⊕ VG) := Classical.choose_spec (hk b) }
  have hv (k : K) : Sum.inr (v k) = (k : VH ⊕ VG) := Classical.choose_spec (hk k)
  let M := {sigma : U → K // PerfectMatching F U K hUK sigma}
  obtain ⟨sigma0⟩ := hmatch
  obtain ⟨y0, hy0⟩ := hY
  let filler := v (sigma0.val (e ⟨y0, hy0⟩))
  let g (sigma : M) (y : VH) : VG :=
    if hy : y ∈ Y then v (sigma.val (e ⟨y, hy⟩)) else filler
  have hg (sigma : M) (y : Y) : g sigma y.1 = v (sigma.val (e y)) := by
    simp only [g, dif_pos y.2]
  have allowed (sigma : M) (y : Y) :
      (UpdatedCandidacy B A X f).allowed y.1 (g sigma y.1) := by
    have hedge := hFA (sigma.property.2 (e y))
    rw [SimpleGraph.fromRel_adj] at hedge
    rcases hedge.2 with hedge | hedge
    · obtain ⟨a, w, ha, hw, haw⟩ := hedge
      rw [he] at ha
      rw [← hv] at hw
      have hay : y.1 = a := Sum.inl.inj ha
      have hwv : v (sigma.val (e y)) = w := Sum.inr.inj hw
      rw [hg, hay, hwv]
      exact haw.2.2
    · obtain ⟨a, w, ha, hw, _⟩ := hedge
      rw [← hv] at ha
      cases ha
  let record (sigma : M) : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y :=
    { toFun := g sigma
      injOn := by
        intro a ha b hb hab
        rw [hg sigma ⟨a, ha⟩, hg sigma ⟨b, hb⟩] at hab
        exact congrArg Subtype.val (e.injective (sigma.property.1.1 (v.injective hab)))
      map_adj := by
        intro a b ha hb hab
        have hai : B.sourceCluster a = i := (Finset.mem_filter.mp ha).2
        have hbi : B.sourceCluster b = i := (Finset.mem_filter.mp hb).2
        have hne : a ≠ b := hab.ne
        exact False.elim (B.source_independent i hai hbi hne hab)
      compatible := fun y hy => allowed sigma ⟨y, hy⟩ }
  have hrecord (sigma : M) (y : Y) :
      (record sigma).toFun y.1 = v (sigma.val (e y)) := hg sigma y
  let lift : M ↪ PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y :=
    { toFun := record
      inj' := by
        intro a b hab
        apply Subtype.ext
        funext u
        obtain ⟨y, rfl⟩ := e.surjective u
        apply v.injective
        rw [← hrecord, ← hrecord]
        exact congrArg (fun z => z.toFun y.1) hab }
  refine ⟨e, v, lift, he, hv, hrecord, ?_⟩
  intro sigma h hold hnew j hij hjS hjround
  have hji : j ≠ i := fun heq => hij.ne heq.symm
  have memX' (x : VH) : x ∈ X' ↔ x ∈ X ∨ x ∈ Y := by
    rw [hX]
    simp only [X', Y, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    tauto
  have source_unused {y : VH} (hyj : B.sourceCluster y = j) : y ∉ X' := by
    simp only [X', Finset.mem_filter, Finset.mem_univ, true_and, hyj,
      Finset.mem_insert]
    exact not_or.mpr ⟨not_lt.mpr hjround, not_or.mpr ⟨hji, hjS⟩⟩
  have host_unused {w : VG} (hwj : B.hostCluster w = j) : w ∉ X'.image h.toFun := by
    intro hw
    obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hw
    have hxj : B.sourceCluster x = j := by
      rw [A.cluster_respecting (h.compatible x hx), hxw, hwj]
    exact source_unused hxj hx
  have transported {y : VH} {w : VG}
      (hyold : (y, w) ∈ UpdatedCandidacyCluster B A X f j)
      (hconstraint : ∀ u : U, (∃ x : VH, (u : VH ⊕ VG) = Sum.inl x ∧ H.Adj x y) →
        ∃ z : VG, (sigma.val u : VH ⊕ VG) = Sum.inr z ∧ G.Adj z w) :
      (y, w) ∈ UpdatedCandidacyCluster B A X' h j := by
    rcases hyold with ⟨hyj, hwj, hyallowed⟩
    refine ⟨hyj, hwj, source_unused hyj, host_unused hwj, hyallowed.2.2.1, ?_⟩
    intro x hx hyx
    rcases (memX' x).mp hx with hxold | hxY
    · rw [hold x hxold]
      exact hyallowed.2.2.2 x hxold hyx
    · let xy : Y := ⟨x, hxY⟩
      obtain ⟨z, hz, hzw⟩ := hconstraint (e xy) ⟨x, he xy, hyx.symm⟩
      have hzv : v (sigma.val (e xy)) = z := Sum.inr.inj ((hv _).trans hz)
      have hhx : h.toFun x = v (sigma.val (e xy)) :=
        (hnew x hxY).trans (hrecord sigma xy)
      rw [hhx, hzv]
      exact hzw.symm
  refine ⟨?_, ?_, ?_⟩
  · intro p s hedge
    rw [SimpleGraph.fromRel_adj] at hedge ⊢
    refine ⟨hedge.1, ?_⟩
    rcases hedge.2 with hedge | hedge
    · obtain ⟨y, w, hp, hs, hyw, hc⟩ := hedge
      exact Or.inl ⟨y, w, hp, hs, transported hyw hc⟩
    · obtain ⟨y, w, hs, hp, hyw, hc⟩ := hedge
      exact Or.inr ⟨y, w, hs, hp, transported hyw hc⟩
  · ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨y, rfl, hyj, _⟩
      exact ⟨y, hyj, rfl⟩
    · rintro ⟨y, hyj, rfl⟩
      refine ⟨y, rfl, hyj, ?_⟩
      simpa only [X', Finset.mem_filter, Finset.mem_univ, true_and] using source_unused hyj
  · ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨w, rfl, hwj, _⟩
      exact ⟨w, hwj, rfl⟩
    · rintro ⟨w, hwj, rfl⟩
      refine ⟨w, rfl, hwj, ?_⟩
      simpa only [X', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        using host_unused hwj
