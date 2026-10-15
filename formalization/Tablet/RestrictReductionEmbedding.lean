import Tablet.BlowUpReductionToAuxiliary
import Tablet.PartialCompatibleEmbedding

-- [TABLET NODE: RestrictReductionEmbedding]
def RestrictReductionEmbedding {r Delta : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H H' : SimpleGraph VH} {G G' : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    {R' : SimpleGraph (Fin r × Fin (Delta ^ 2))}
    (B : BlowUpInstance r VH VG H G R)
    (A : CandidacySystem B)
    (B' : BlowUpInstance (r * Delta ^ 2) VH VG H' G'
      (R'.comap finProdFinEquiv.symm))
    (A' : CandidacySystem B')
    (hH : H ≤ H') (hG : G' ≤ G)
    (hA : ∀ {x v}, A'.allowed x v → A.allowed x v)
    (_hSource : ∀ x, (finProdFinEquiv.symm (B'.sourceCluster x)).1 = B.sourceCluster x)
    (_hHost : ∀ v, (finProdFinEquiv.symm (B'.hostCluster v)).1 = B.hostCluster v)
    (φ : SimpleGraph.Copy H' G') (hφ : CompatibleEmbedding B' A' φ) :
    PartialCompatibleEmbedding B A Finset.univ :=
-- BODY
  { toFun := φ
    injOn := φ.injective.injOn
    map_adj := fun _ _ hxy => hG (φ.toHom.map_rel' (hH hxy))
    compatible := fun x _ => hA (hφ x) }
