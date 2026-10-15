import Tablet.Preamble
import Tablet.BipartiteRectangleDegreeBound
import Tablet.BipartiteFactorCutCapacity
import Tablet.RectangleFactorCutLowerBound
import Tablet.IntegralFlowTerminalCut
import Tablet.BipartiteFlowSaturation
import Tablet.BipartiteSelectedEdgeGraph

open scoped BigOperators

-- [TABLET NODE: BipartiteRegularFactorCriterion]
theorem BipartiteRegularFactorCriterion :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
      (hUW : Disjoint U W) (k : ℕ), U.card = W.card →
      ((∃ F : SimpleGraph V, F ≤ G ∧
          (∀ u ∈ U, {w | w ∈ W ∧ F.Adj u w}.ncard = k) ∧
          (∀ w ∈ W, {u | u ∈ U ∧ F.Adj u w}.ncard = k)) ↔
        ∀ A ⊆ U, ∀ B ⊆ W,
          k * (A.card + B.card - U.card) ≤
            ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card) := by
-- BODY
  classical
  intro V _ _ G _ U W hUW k hsize
  constructor
  · rintro ⟨F, hFG, hU, hW⟩ A hA B hB
    have hcount (T : Finset V) (P : V → Prop) :
        (T.filter P).card = {v | v ∈ T ∧ P v}.ncard := by
      have he : {v | v ∈ T ∧ P v} = (T.filter P : Set V) := by
        ext v
        simp
      rw [he, Set.ncard_coe_finset]
    have hrow : ∀ u ∈ U, k ≤ (W.filter fun w => F.Adj u w).card := by
      intro u hu
      rw [hcount, hU u hu]
    have hcol : ∀ w ∈ W, (U.filter fun u => F.Adj u w).card ≤ k := by
      intro w hw
      rw [hcount, hW w hw]
    have h := BipartiteRectangleDegreeBound U W F.Adj k hrow hcol A B hA hB
    rw [← hsize] at h
    refine h.trans (Finset.card_le_card ?_)
    intro p hp
    obtain ⟨hp, hf⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, hFG hf⟩
  · intro hrect
    let N := BipartiteFactorNetwork G U W k
    obtain ⟨f, S, hs, ht, hcut, _, hupper⟩ := IntegralFlowTerminalCut N
    obtain ⟨hsource, hformula⟩ := BipartiteFactorCutCapacity G U W k
    obtain ⟨A, B, hA, hB, hformula⟩ := hformula S hs ht
    have hlower := RectangleFactorCutLowerBound G U W k hsize hrect A B hA hB
    have hvalue : (∑ w, f.amount N.source w) = ((k * U.card : ℕ) : ℤ) := by
      rw [hcut, hformula] at hupper ⊢
      rw [hsource] at hupper
      exact le_antisymm hupper (by exact_mod_cast hlower)
    obtain ⟨_, _, hmiddle, hrow, hcol⟩ :=
      BipartiteFlowSaturation G U W k hsize f hvalue
    let P : U → W → Prop := fun u w =>
      f.amount (Sum.inl (some u)) (Sum.inr (some w)) = 1
    obtain ⟨F, hFG, hU, hW, _⟩ := BipartiteSelectedEdgeGraph G U W hUW P k
      (fun u w h => (hmiddle u w).2.2 h) hrow hcol
    exact ⟨F, hFG, hU, hW⟩
