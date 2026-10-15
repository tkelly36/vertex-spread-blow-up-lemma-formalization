import Tablet.CompatibleEmbedding

-- [TABLET NODE: PartialCompatibleEmbedding]
structure PartialCompatibleEmbedding {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B) (X : Finset VH) where
-- BODY
  toFun : VH → VG
  injOn : Set.InjOn toFun X
  map_adj : ∀ {x y}, x ∈ X → y ∈ X → H.Adj x y → G.Adj (toFun x) (toFun y)
  compatible : ∀ x ∈ X, A.allowed x (toFun x)
