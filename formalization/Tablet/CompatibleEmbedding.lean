import Tablet.CandidacySystem
import Mathlib.Combinatorics.SimpleGraph.Copy

-- [TABLET NODE: CompatibleEmbedding]
def CompatibleEmbedding {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (φ : SimpleGraph.Copy H G) : Prop :=
-- BODY
  ∀ x, A.allowed x (φ x)
