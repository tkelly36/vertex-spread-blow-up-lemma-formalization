import Tablet.UpdatedCandidacy

-- [TABLET NODE: UpdatedCandidacyCluster]
def UpdatedCandidacyCluster {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VG] {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B) (X : Finset VH)
    (f : PartialCompatibleEmbedding B A X) (i : Fin r) : Set (VH × VG) :=
-- BODY
  {p | B.sourceCluster p.1 = i ∧ B.hostCluster p.2 = i ∧
    (UpdatedCandidacy B A X f).allowed p.1 p.2}
