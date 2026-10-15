import Tablet.CandidacySystem

-- [TABLET NODE: RawCandidates]
noncomputable def RawCandidates {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (S : Finset VH) (f : VH → VG) (x : VH) : Finset VG := by
-- BODY
  classical
  exact Finset.univ.filter fun v =>
    A.allowed x v ∧ ∀ y ∈ S, H.Adj x y → G.Adj v (f y)
