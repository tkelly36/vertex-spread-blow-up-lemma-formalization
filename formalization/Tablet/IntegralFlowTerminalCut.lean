import Tablet.IntegralFlowAugmentation
import Tablet.IntegralFlowCutIdentity
import Tablet.DirectedReachabilitySimplePath

open scoped BigOperators

-- [TABLET NODE: IntegralFlowTerminalCut]
theorem IntegralFlowTerminalCut {V : Type*} [Fintype V] [DecidableEq V]
    (N : FiniteCapacityNetwork V) :
    ∃ (f : FiniteIntegralFlow N) (S : Finset V),
      N.source ∈ S ∧ N.sink ∉ S ∧
      (∑ w, f.amount N.source w) =
        ∑ v ∈ S, ∑ w ∈ Finset.univ \ S, (N.capacity v w : ℤ) ∧
      0 ≤ (∑ w, f.amount N.source w) ∧
      (∑ w, f.amount N.source w) ≤ ∑ w, (N.capacity N.source w : ℤ) := by
-- BODY
  classical
  let value (f : FiniteIntegralFlow N) : ℤ := ∑ w, f.amount N.source w
  let M : ℤ := ∑ w, (N.capacity N.source w : ℤ)
  have hbound (f : FiniteIntegralFlow N) : value f ≤ M := by
    exact Finset.sum_le_sum (fun w _ => f.bound N.source w)
  have hterminal : ∀ n : ℕ, ∀ f : FiniteIntegralFlow N,
      0 ≤ value f → (M - value f).toNat = n →
      ∃ g : FiniteIntegralFlow N, 0 ≤ value g ∧ ¬Nonempty (SimpleResidualPath g) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hn
      by_cases hp : Nonempty (SimpleResidualPath f)
      · obtain ⟨p⟩ := hp
        obtain ⟨δ, g, hδ, _, _, hval⟩ := IntegralFlowAugmentation f p
        change value g = value f + δ at hval
        have hg : 0 ≤ value g := by omega
        have hfb := hbound f
        have hgb := hbound g
        have hsmall : (M - value g).toNat < n := by omega
        exact ih (M - value g).toNat hsmall g hg rfl
      · exact ⟨f, hf, hp⟩
  let zero : FiniteIntegralFlow N := {
    amount := fun _ _ => 0
    skew := by intros; simp
    bound := by intros; positivity
    conserve := by intros; simp }
  have hzero : 0 ≤ value zero := by simp [value, zero]
  obtain ⟨f, hf, hno⟩ := hterminal (M - value zero).toNat zero hzero rfl
  let R (v w : V) : Prop := f.amount v w < (N.capacity v w : ℤ)
  let S : Finset V := Finset.univ.filter (Relation.ReflTransGen R N.source)
  have hmem (v : V) : v ∈ S ↔ Relation.ReflTransGen R N.source v := by
    simp [S]
  have hs : N.source ∈ S := (hmem _).mpr .refl
  have hclosed (v w : V) (hv : v ∈ S) (hr : R v w) : w ∈ S :=
    (hmem _).mpr ((hmem _).mp hv |>.tail hr)
  have ht : N.sink ∉ S := by
    intro ht
    obtain ⟨n, p, hpos, hinj, hstart, hfinish, hres⟩ :=
      DirectedReachabilitySimplePath R ((hmem _).mp ht) N.terminals_distinct
    exact hno ⟨{
      length := n
      positive := hpos
      vertex := p
      injective := hinj
      start := hstart
      finish := hfinish
      residual := hres }⟩
  have heq (v w : V) (hv : v ∈ S) (hw : w ∉ S) :
      f.amount v w = (N.capacity v w : ℤ) := by
    have hn : ¬R v w := fun hr => hw (hclosed v w hv hr)
    exact le_antisymm (f.bound v w) (le_of_not_gt hn)
  refine ⟨f, S, hs, ht, ?_, hf, hbound f⟩
  rw [IntegralFlowCutIdentity f S hs ht]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  exact heq v w hv (Finset.mem_sdiff.mp hw).2
