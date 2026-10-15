import Tablet.UpdatedCandidacy

-- [TABLET NODE: UpdatedCandidacyCongruence]
theorem UpdatedCandidacyCongruence {r : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B) (X : Finset VH)
    (f g : PartialCompatibleEmbedding B A X)
    (h : ∀ x ∈ X, f.toFun x = g.toFun x) :
    ∀ x v, (UpdatedCandidacy B A X f).allowed x v ↔
      (UpdatedCandidacy B A X g).allowed x v := by
-- BODY
  classical
  have himage : X.image f.toFun = X.image g.toFun := by
    apply Finset.image_congr
    exact h
  intro x v
  change (x ∉ X ∧ v ∉ X.image f.toFun ∧ A.allowed x v ∧
      ∀ y ∈ X, H.Adj x y → G.Adj v (f.toFun y)) ↔
    (x ∉ X ∧ v ∉ X.image g.toFun ∧ A.allowed x v ∧
      ∀ y ∈ X, H.Adj x y → G.Adj v (g.toFun y))
  rw [himage]
  constructor
  · rintro ⟨hx, hv, ha, he⟩
    refine ⟨hx, hv, ha, ?_⟩
    intro y hy hxy
    rw [← h y hy]
    exact he y hy hxy
  · rintro ⟨hx, hv, ha, he⟩
    refine ⟨hx, hv, ha, ?_⟩
    intro y hy hxy
    rw [h y hy]
    exact he y hy hxy
