import Tablet.UpdatedCandidacyCluster
import Tablet.VertexSpreadOn
import Tablet.SuperRegularPair
import Tablet.PartialCompatibleEmbedding

-- [TABLET NODE: ColourRoundInvariant]
def ColourRoundInvariant {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (epsilon density : ℕ → ENNReal)
    (D : ℕ) (C : ENNReal) (n round : ℕ) (touched : Finset (Fin r))
    (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X)) : Prop :=
-- BODY
  round < q ∧
  (∀ j : Fin r, (Finset.univ.filter fun k : Fin r => R.Adj j k).card ≤ D) ∧
  (∀ ⦃i j : Fin r⦄, i ≠ j →
    (R.Adj i j ∨ ∃ k : Fin r, R.Adj i k ∧ R.Adj k j) →
    colour i ≠ colour j) ∧
  (∀ j ∈ touched, (colour j).val = round) ∧
  X = Finset.univ.filter (fun x =>
    (colour (B.sourceCluster x)).val < round ∨ B.sourceCluster x ∈ touched) ∧
    VertexSpreadOn (μ.map fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1)
      (C / n) Set.univ ∧
    ∀ f ∈ μ.support, ∀ j : Fin r, j ∉ touched → round ≤ (colour j).val →
      let exposure := (Finset.univ.filter fun k : Fin r =>
        ((colour k).val < round ∨ k ∈ touched) ∧ R.Adj j k).card
      let touchedNeighbors := touched.filter fun k => R.Adj j k
      let witnessError := if touchedNeighbors.Nonempty then epsilon (round + 1) else epsilon round
      let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ y : VH, z = Sum.inl y ∧ B.sourceCluster y = j ∧ y ∉ X
      let Vused : Finset VG := X.image f.toFun
      let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = j ∧ v ∉ Vused
      let Aⱼ : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p s =>
        ∃ y : VH, ∃ v : VG, p = Sum.inl y ∧ s = Sum.inr v ∧
          (y, v) ∈ UpdatedCandidacyCluster B A X f j
      exposure ≤ D ∧ touchedNeighbors.card ≤ 1 ∧
      ∃ W : SimpleGraph (VH ⊕ VG), W ≤ Aⱼ ∧
        @SuperRegularPair (VH ⊕ VG) _ W (Classical.decRel _)
          L Q witnessError (density exposure)
