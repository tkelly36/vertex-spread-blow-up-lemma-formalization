import Tablet.BlowUpInstance

-- [TABLET NODE: PaddedSource]
abbrev PaddedSource {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) :=
-- BODY
  VH ⊕ (Σ i : Fin r, Fin (Fintype.card {v : VG // B.hostCluster v = i} -
    Fintype.card {x : VH // B.sourceCluster x = i}))
