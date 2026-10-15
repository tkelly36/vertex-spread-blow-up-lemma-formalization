import Tablet.Preamble

-- [TABLET NODE: BlowUpInstance]
structure BlowUpInstance (r : ℕ) (VH VG : Type*) [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (R : SimpleGraph (Fin r)) where
-- BODY
  sourceCluster : VH → Fin r
  hostCluster : VG → Fin r
  source_independent : ∀ i, H.IsIndepSet {x | sourceCluster x = i}
  capacity : ∀ i, Fintype.card {x | sourceCluster x = i} ≤
    Fintype.card {v | hostCluster v = i}
  reduced_support : ∀ {x y}, H.Adj x y → R.Adj (sourceCluster x) (sourceCluster y)
