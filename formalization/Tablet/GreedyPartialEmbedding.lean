import Tablet.RawCandidates
import Tablet.PartialCompatibleEmbedding

-- [TABLET NODE: GreedyPartialEmbedding]
structure GreedyPartialEmbedding {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel H.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (d ε : ENNReal) (n : ℕ) (S : Finset VH)
    extends PartialCompatibleEmbedding B A S where
-- BODY
  raw_bound : ∀ x, x ∉ S →
    d * (d - ε) ^ (S.filter fun y => H.Adj x y).card * n ≤
      (RawCandidates B A S toFun x).card
