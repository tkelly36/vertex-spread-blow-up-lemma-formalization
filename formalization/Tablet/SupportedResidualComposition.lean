import Tablet.UpdatedCandidacy
import Tablet.VertexSpreadSequential

-- [TABLET NODE: SupportedResidualComposition]
theorem SupportedResidualComposition
    {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG}
    {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X)) (q : ENNReal)
    (hμ : VertexSpreadOn
      (μ.map fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1) q Set.univ)
    (hres : ∀ f : PartialCompatibleEmbedding B A X, μ f ≠ 0 →
      let Y := {x : VH // x ∉ X}
      let W := {v : VG // v ∉ X.image f.toFun}
      ∃ Br : BlowUpInstance r Y W
          (H.induce {x : VH | x ∉ X})
          (G.induce {v : VG | v ∉ X.image f.toFun}) R,
      ∃ Ar : CandidacySystem Br,
        (∀ x : Y, Br.sourceCluster x = B.sourceCluster x.1) ∧
        (∀ v : W, Br.hostCluster v = B.hostCluster v.1) ∧
        (∀ (x : Y) (v : W), Ar.allowed x v ↔
          (UpdatedCandidacy B A X f).allowed x.1 v.1) ∧
        ∃ ν : PMF {φ : SimpleGraph.Copy
            (H.induce {x : VH | x ∉ X})
            (G.induce {v : VG | v ∉ X.image f.toFun}) // CompatibleEmbedding Br Ar φ},
          VertexSpreadOn (ν.map fun φ => fun x => φ.1 x) q Set.univ) :
    ∃ ν : PMF {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ},
      VertexSpreadOn (ν.map fun φ => fun x => φ.1 x) q Set.univ := by
-- BODY
  classical
  dsimp only at hres
  choose Br Ar hs hv ha ν hν using hres
  let glue (f : PartialCompatibleEmbedding B A X) (hf : μ f ≠ 0)
      (φ : {φ : SimpleGraph.Copy (H.induce {x | x ∉ X})
        (G.induce {v | v ∉ X.image f.toFun}) // CompatibleEmbedding (Br f hf) (Ar f hf) φ}) :
      {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ} := by
    let g : VH → VG := fun x => if hx : x ∈ X then f.toFun x else (φ.1 ⟨x, hx⟩).1
    have hgX (x : VH) (hx : x ∈ X) : g x = f.toFun x := dif_pos hx
    have hgY (x : VH) (hx : x ∉ X) : g x = (φ.1 ⟨x, hx⟩).1 := dif_neg hx
    have hgnot (x : VH) (hx : x ∉ X) : g x ∉ X.image f.toFun := by
      rw [hgY x hx]
      exact (φ.1 ⟨x, hx⟩).2
    have hginj : Function.Injective g := by
      intro x y heq
      by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
      · rw [hgX x hx, hgX y hy] at heq
        exact f.injOn hx hy heq
      · exact False.elim (hgnot y hy (heq ▸ Finset.mem_image.mpr ⟨x, hx, (hgX x hx).symm⟩))
      · exact False.elim (hgnot x hx (heq ▸ Finset.mem_image.mpr ⟨y, hy, (hgX y hy).symm⟩))
      · rw [hgY x hx, hgY y hy] at heq
        exact congrArg Subtype.val (φ.1.injective (Subtype.ext heq))
    have hallowed (x : VH) (hx : x ∉ X) :
        (UpdatedCandidacy B A X f).allowed x (g x) := by
      rw [hgY x hx]
      exact (ha f hf ⟨x, hx⟩ (φ.1 ⟨x, hx⟩)).mp (φ.2 ⟨x, hx⟩)
    refine ⟨{ toHom := { toFun := g, map_rel' := ?_ }, injective' := hginj }, ?_⟩
    · intro x y hxy
      by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
      · rw [hgX x hx, hgX y hy]
        exact f.map_adj hx hy hxy
      · rw [hgX x hx]
        exact ((hallowed y hy).2.2.2 x hx hxy.symm).symm
      · rw [hgX y hy]
        exact (hallowed x hx).2.2.2 y hy hxy
      · rw [hgY x hx, hgY y hy]
        exact φ.1.toHom.map_rel' (show (H.induce {x | x ∉ X}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · intro x
      by_cases hx : x ∈ X
      · change A.allowed x (g x)
        rw [hgX x hx]
        exact f.compatible x hx
      · exact (hallowed x hx).2.2.1
  have glueX (f) (hf : μ f ≠ 0) (φ) (x : VH) (hx : x ∈ X) :
      (glue f hf φ).1 x = f.toFun x := by
    change (if hz : x ∈ X then f.toFun x else (φ.1 ⟨x, hz⟩).1) = _
    exact dif_pos hx
  have glueY (f) (hf : μ f ≠ 0) (φ) (x : VH) (hx : x ∉ X) :
      (glue f hf φ).1 x = (φ.1 ⟨x, hx⟩).1 := by
    change (if hz : x ∈ X then f.toFun x else (φ.1 ⟨x, hz⟩).1) = _
    exact dif_neg hx
  let κ := fun f (hf : μ f ≠ 0) => (ν f hf).map (glue f hf)
  refine ⟨μ.bindOnSupport κ, hμ.1, ?_⟩
  intro s x y hx _
  let L := {i : Fin s // x i ∈ X}
  let T := {i : Fin s // x i ∉ X}
  let a := Fintype.card L
  let b := Fintype.card T
  let eL := Fintype.equivFin L
  let eT := Fintype.equivFin T
  let left : L → {x : VH // x ∈ X} := fun i => ⟨x i.1, i.2⟩
  let right : T → {x : VH // x ∉ X} := fun i => ⟨x i.1, i.2⟩
  have hleft : Function.Injective left := by
    intro i j hij
    exact Subtype.ext (hx (congrArg Subtype.val hij))
  have hright : Function.Injective right := by
    intro i j hij
    exact Subtype.ext (hx (congrArg Subtype.val hij))
  have hab : a + b = s := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sumCompl (fun i : Fin s => x i ∈ X))
  let EL : Set (PartialCompatibleEmbedding B A X) := {f | ∀ i : L, f.toFun (x i.1) = y i.1}
  have hEL : μ.toOuterMeasure EL ≤ q ^ a := by
    have hc : (fun f : PartialCompatibleEmbedding B A X =>
        fun z : {x : VH // x ∈ X} => f.toFun z.1) ⁻¹'
        CylinderEvent (fun j : Fin a => left (eL.symm j))
          (fun j => y (eL.symm j).1) = EL := by
      ext f
      change (∀ j, f.toFun (x (eL.symm j).1) = y (eL.symm j).1) ↔
        ∀ i : L, f.toFun (x i.1) = y i.1
      exact ⟨fun h i => by simpa only [Equiv.symm_apply_apply] using h (eL i),
        fun h j => h (eL.symm j)⟩
    have h := hμ.2 a (fun j => left (eL.symm j)) (fun j => y (eL.symm j).1)
      (hleft.comp eL.symm.injective) (fun _ => Set.mem_univ _)
    rwa [PMF.toOuterMeasure_map_apply, hc] at h
  let E : Set {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ} :=
    {φ | ∀ i, φ.1 (x i) = y i}
  have conditional (f) (hf : μ f ≠ 0) :
      (κ f hf).toOuterMeasure E ≤ if f ∈ EL then q ^ b else 0 := by
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hfL : f ∈ EL
    · rw [if_pos hfL]
      by_cases htargets : ∀ i : T, y i.1 ∉ X.image f.toFun
      · let target : T → {v : VG // v ∉ X.image f.toFun} := fun i => ⟨y i.1, htargets i⟩
        have hc : (fun φ => fun z => φ.1 z) ⁻¹'
            CylinderEvent (fun j : Fin b => right (eT.symm j))
              (fun j => target (eT.symm j)) =
            (glue f hf) ⁻¹' E := by
          ext φ
          change (∀ j, φ.1 (right (eT.symm j)) = target (eT.symm j)) ↔
            ∀ i, (glue f hf φ).1 (x i) = y i
          constructor
          · intro h i
            by_cases hi : x i ∈ X
            · rw [glueX f hf φ (x i) hi]
              exact hfL ⟨i, hi⟩
            · rw [glueY f hf φ (x i) hi]
              have ht := congrArg Subtype.val (h (eT ⟨i, hi⟩))
              simpa only [Equiv.symm_apply_apply] using ht
          · intro h j
            apply Subtype.ext
            simpa only [glueY f hf φ (x (eT.symm j).1) (eT.symm j).2] using
              h (eT.symm j).1
        have h := (hν f hf).2 b (fun j => right (eT.symm j))
          (fun j => target (eT.symm j)) (hright.comp eT.symm.injective)
          (fun _ => Set.mem_univ _)
        rw [PMF.toOuterMeasure_map_apply] at h
        rw [← hc]
        exact h
      · have hempty : (glue f hf) ⁻¹' E = ∅ := by
          ext φ
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hE
          apply htargets
          intro i
          have heq := hE i.1
          rw [glueY f hf φ (x i.1) i.2] at heq
          rw [← heq]
          exact (φ.1 ⟨x i.1, i.2⟩).2
        rw [hempty]
        exact (ν f hf).toOuterMeasure.empty.trans_le (zero_le _)
    · rw [if_neg hfL]
      have hempty : (glue f hf) ⁻¹' E = ∅ := by
        ext φ
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro hE
        apply hfL
        intro i
        simpa only [glueX f hf φ (x i.1) i.2] using hE i.1
      rw [hempty]
      exact (ν f hf).toOuterMeasure.empty.le
  rw [PMF.toOuterMeasure_map_apply]
  change (μ.bindOnSupport κ).toOuterMeasure E ≤ q ^ s
  calc
    _ = ∑' f, μ f * if hf : μ f = 0 then 0 else (κ f hf).toOuterMeasure E :=
      PMF.toOuterMeasure_bindOnSupport_apply _ _
    _ ≤ ∑' f, (if f ∈ EL then μ f else 0) * q ^ b := by
      apply ENNReal.tsum_le_tsum
      intro f
      by_cases hf : μ f = 0
      · simp only [hf, zero_mul, ite_self]
        exact le_rfl
      · rw [dif_neg hf]
        have h := mul_le_mul_left' (conditional f hf) (μ f)
        by_cases hfL : f ∈ EL <;>
          simpa only [hfL, if_true, if_false, mul_zero, zero_mul] using h
    _ = μ.toOuterMeasure EL * q ^ b := by
      rw [ENNReal.tsum_mul_right, PMF.toOuterMeasure_apply]
      simp only [Set.indicator_apply]
    _ ≤ q ^ a * q ^ b := mul_le_mul_right' hEL _
    _ = q ^ s := by rw [← pow_add, hab]
