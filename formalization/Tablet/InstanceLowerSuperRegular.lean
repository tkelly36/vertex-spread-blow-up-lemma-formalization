import Tablet.BlowUpInstance
import Tablet.LowerSuperRegularPair

-- [TABLET NODE: InstanceLowerSuperRegular]
def InstanceLowerSuperRegular {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VG] {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel G.Adj]
    {R : SimpleGraph (Fin r)} (B : BlowUpInstance r VH VG H G R) (ε d : ENNReal) : Prop :=
-- BODY
  ∀ ⦃i j⦄, R.Adj i j →
    LowerSuperRegularPair G (Finset.univ.filter fun v => B.hostCluster v = i)
      (Finset.univ.filter fun v => B.hostCluster v = j) ε d
