import Tablet.BlowUpInstance

-- [TABLET NODE: CandidacySystem]
structure CandidacySystem {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) where
-- BODY
  allowed : VH → VG → Prop
  cluster_respecting : ∀ {x v}, allowed x v → B.sourceCluster x = B.hostCluster v
