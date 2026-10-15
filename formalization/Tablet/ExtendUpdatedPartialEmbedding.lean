import Tablet.UpdatedCandidacy

-- [TABLET NODE: ExtendUpdatedPartialEmbedding]
theorem ExtendUpdatedPartialEmbedding {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X Y : Finset VH) (hXY : Disjoint X Y)
    (f : PartialCompatibleEmbedding B A X)
    (g : PartialCompatibleEmbedding B (UpdatedCandidacy B A X f) Y) :
    ∃ h : PartialCompatibleEmbedding B A (X ∪ Y),
      (∀ x ∈ X, h.toFun x = f.toFun x) ∧
      (∀ y ∈ Y, h.toFun y = g.toFun y) := by
-- BODY
  let h : VH → VG := fun z => if z ∈ X then f.toFun z else g.toFun z
  have hX : ∀ x ∈ X, h x = f.toFun x := by
    intro x hx
    simp only [h, if_pos hx]
  have hY : ∀ y ∈ Y, h y = g.toFun y := by
    intro y hy
    have hyX : y ∉ X := fun hx => Finset.disjoint_left.mp hXY hx hy
    simp only [h, if_neg hyX]
  refine ⟨{ toFun := h, injOn := ?_, map_adj := ?_, compatible := ?_ }, hX, hY⟩
  · intro x hx y hy heq
    change x ∈ X ∪ Y at hx
    change y ∈ X ∪ Y at hy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · rw [hX x hx, hX y hy] at heq
      exact f.injOn hx hy heq
    · rw [hX x hx, hY y hy] at heq
      exact False.elim ((g.compatible y hy).2.1
        (Finset.mem_image.mpr ⟨x, hx, heq⟩))
    · rw [hY x hx, hX y hy] at heq
      exact False.elim ((g.compatible x hx).2.1
        (Finset.mem_image.mpr ⟨y, hy, heq.symm⟩))
    · rw [hY x hx, hY y hy] at heq
      exact g.injOn hx hy heq
  · intro x y hx hy hadj
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · rw [hX x hx, hX y hy]
      exact f.map_adj hx hy hadj
    · rw [hX x hx, hY y hy]
      exact G.symm ((g.compatible y hy).2.2.2 x hx (H.symm hadj))
    · rw [hY x hx, hX y hy]
      exact (g.compatible x hx).2.2.2 y hy hadj
    · rw [hY x hx, hY y hy]
      exact g.map_adj hx hy hadj
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [hX z hz]
      exact f.compatible z hz
    · rw [hY z hz]
      exact (g.compatible z hz).2.2.1
