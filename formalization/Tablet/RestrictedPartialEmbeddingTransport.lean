import Tablet.UpdatedCandidacy
import Tablet.VertexSpreadRestriction

-- [TABLET NODE: RestrictedPartialEmbeddingTransport]
theorem RestrictedPartialEmbeddingTransport {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (S X : Finset VH) (hXS : X ⊆ S)
    (Bs : BlowUpInstance r {x // x ∈ S} VG (H.induce (S : Set VH)) G R)
    (As : CandidacySystem Bs)
    (hallowed : ∀ (x : {x // x ∈ S}) v, As.allowed x v ↔ A.allowed x.1 v)
    (T : Finset {x // x ∈ S}) (hT : ∀ x, x ∈ T ↔ x.1 ∈ X)
    (g : VH → VG) (q rho : ENNReal)
    (ν : PMF {f : PartialCompatibleEmbedding Bs As T //
      ∀ x, x ∉ T → rho ≤ Set.ncard
        {v : VG | (UpdatedCandidacy Bs As T f).allowed x v}})
    (hν : VertexSpreadOn (ν.map fun f => f.val.toFun) q Set.univ) :
    ∃ μ : PMF (PartialCompatibleEmbedding B A X),
      VertexSpreadOn (μ.map fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1)
        q Set.univ ∧
      ∀ f, μ f ≠ 0 → ∀ x ∈ S, x ∉ X →
        rho ≤ Set.ncard {v : VG | (UpdatedCandidacy B A X f).allowed x v} := by
-- BODY
  classical
  let liftX (x : VH) (hx : x ∈ X) : {x // x ∈ S} := ⟨x, hXS hx⟩
  let extend (t : PartialCompatibleEmbedding Bs As T) :
      PartialCompatibleEmbedding B A X :=
    { toFun := fun x => if hx : x ∈ X then t.toFun (liftX x hx) else g x
      injOn := by
        intro x hx y hy hxy
        change x ∈ X at hx
        change y ∈ X at hy
        have heq : t.toFun (liftX x hx) = t.toFun (liftX y hy) := by
          simpa [hx, hy] using hxy
        exact congrArg Subtype.val
          (t.injOn ((hT _).mpr hx) ((hT _).mpr hy) heq)
      map_adj := by
        intro x y hx hy hxy
        simpa only [dif_pos hx, dif_pos hy] using
          t.map_adj (x := liftX x hx) (y := liftX y hy)
            ((hT _).mpr hx) ((hT _).mpr hy) hxy
      compatible := by
        intro x hx
        simpa only [dif_pos hx] using
          (hallowed (liftX x hx) _).mp (t.compatible _ ((hT _).mpr hx)) }
  have hext (t : PartialCompatibleEmbedding Bs As T) (x : VH) (hx : x ∈ X) :
      (extend t).toFun x = t.toFun (liftX x hx) := by
    simp only [extend, dif_pos hx]
  have himage (t : PartialCompatibleEmbedding Bs As T) :
      X.image (extend t).toFun = T.image t.toFun := by
    ext v
    constructor
    · rintro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨liftX x hx, (hT _).mpr hx, (hext t x hx).symm⟩
    · rintro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨x.1, (hT x).mp hx, hext t x.1 ((hT x).mp hx)⟩
  have hupdate (t : PartialCompatibleEmbedding Bs As T) (x : {x // x ∈ S})
      (v : VG) : (UpdatedCandidacy B A X (extend t)).allowed x.1 v ↔
        (UpdatedCandidacy Bs As T t).allowed x v := by
    change (x.1 ∉ X ∧ v ∉ X.image (extend t).toFun ∧ A.allowed x.1 v ∧
      ∀ y ∈ X, H.Adj x.1 y → G.Adj v ((extend t).toFun y)) ↔
      (x ∉ T ∧ v ∉ T.image t.toFun ∧ As.allowed x v ∧
      ∀ y ∈ T, (H.induce (S : Set VH)).Adj x y → G.Adj v (t.toFun y))
    rw [himage t]
    constructor
    · rintro ⟨hx, hv, ha, he⟩
      refine ⟨fun ht => hx ((hT x).mp ht), hv, (hallowed x v).mpr ha, ?_⟩
      intro y hy hxy
      have hyX := (hT y).mp hy
      simpa only [hext t y.1 hyX] using he y.1 hyX hxy
    · rintro ⟨hx, hv, ha, he⟩
      refine ⟨fun ht => hx ((hT x).mpr ht), hv, (hallowed x v).mp ha, ?_⟩
      intro y hy hxy
      rw [hext t y hy]
      exact he (liftX y hy) ((hT _).mpr hy) hxy
  let pack := fun u : {f : PartialCompatibleEmbedding Bs As T //
      ∀ x, x ∉ T → rho ≤ Set.ncard
        {v : VG | (UpdatedCandidacy Bs As T f).allowed x v}} => extend u.val
  let e : {x : VH // x ∈ X} ↪ {x : VH // x ∈ S} :=
    { toFun := fun x => liftX x.1 x.2
      inj' := by
        intro x y h
        exact Subtype.ext (congrArg (fun z : {x : VH // x ∈ S} => z.1) h) }
  refine ⟨ν.map pack, ?_, ?_⟩
  · have hm : (ν.map pack).map
        (fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1) =
        (ν.map fun f => f.val.toFun).map (fun f => f ∘ e) := by
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext u x
      exact hext u.val x.1 x.2
    rw [hm]
    exact VertexSpreadRestriction e hν
  · intro f hf x hxS hxX
    change f ∈ (ν.map pack).support at hf
    obtain ⟨u, _, hu⟩ := (PMF.mem_support_map_iff _ _ _).mp hf
    subst f
    have hc : {v : VG | (UpdatedCandidacy B A X (pack u)).allowed x v} =
        {v : VG | (UpdatedCandidacy Bs As T u.val).allowed ⟨x, hxS⟩ v} := by
      ext v
      exact hupdate u.val ⟨x, hxS⟩ v
    rw [hc]
    exact u.property ⟨x, hxS⟩ (fun ht => hxX ((hT _).mp ht))
