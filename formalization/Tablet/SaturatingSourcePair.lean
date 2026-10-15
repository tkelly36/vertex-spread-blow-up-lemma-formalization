import Tablet.BlowUpInstance

-- [TABLET NODE: SaturatingSourcePair]
def SaturatingSourcePair {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (i j : Fin r) : Prop :=
-- BODY
  (∃ τ : {x : VH // B.sourceCluster x = i} ↪ {y : VH // B.sourceCluster y = j},
      ∀ x y, H.Adj x.1 y.1 ↔ y = τ x) ∨
  (∃ τ : {y : VH // B.sourceCluster y = j} ↪ {x : VH // B.sourceCluster x = i},
      ∀ x y, H.Adj x.1 y.1 ↔ x = τ y)
