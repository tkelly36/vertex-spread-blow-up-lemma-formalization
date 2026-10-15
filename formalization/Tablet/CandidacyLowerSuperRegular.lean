import Tablet.CandidacySystem
import Tablet.LowerSuperRegularPair

-- [TABLET NODE: CandidacyLowerSuperRegular]
def CandidacyLowerSuperRegular {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B) (ε d : ENNReal) : Prop :=
-- BODY
  ∀ j : Fin r,
    let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ x : VH, z = Sum.inl x ∧ B.sourceCluster x = j
    let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
      ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j
    let Aⱼ : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
      ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ q = Sum.inr v ∧ A.allowed x v
    letI : DecidableRel Aⱼ.Adj := Classical.decRel _
    LowerSuperRegularPair Aⱼ L Q ε d
