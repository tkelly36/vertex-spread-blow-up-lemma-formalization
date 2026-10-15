import Tablet.PartialCompatibleEmbedding

-- [TABLET NODE: UpdatedCandidacy]
def UpdatedCandidacy {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VG] {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B) (X : Finset VH)
    (f : PartialCompatibleEmbedding B A X) : CandidacySystem B :=
-- BODY
  { allowed := fun x v =>
      x ∉ X ∧ v ∉ X.image f.toFun ∧ A.allowed x v ∧
        ∀ x' ∈ X, H.Adj x x' → G.Adj v (f.toFun x')
    cluster_respecting := fun h => A.cluster_respecting h.2.2.1 }
