import Tablet.PerfectMatching
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi

-- [TABLET NODE: MatchingPartitionRestrictionCount]
theorem MatchingPartitionRestrictionCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (hUW : Disjoint U W)
    (L R : Fin 4 → Finset V)
    (hL : ∀ i, L i ⊆ U) (hR : ∀ i, R i ⊆ W)
    (hcover : ∀ u ∈ U, ∃ i, u ∈ L i) :
    {f : U → W | PerfectMatching G U W hUW f ∧
      ∀ i, ((L i).attach.image fun u =>
        (f ⟨u.1, hL i u.2⟩).1) = R i}.ncard ≤
    ∏ i, {g : L i → R i |
      PerfectMatching G (L i) (R i) (hUW.mono (hL i) (hR i)) g}.ncard := by
-- BODY
  classical
  let Q := {f : U → W | PerfectMatching G U W hUW f ∧
    ∀ i, ((L i).attach.image fun u => (f ⟨u.1, hL i u.2⟩).1) = R i}
  let P := fun i => {g : L i → R i |
    PerfectMatching G (L i) (R i) (hUW.mono (hL i) (hR i)) g}
  have hmaps (f : Q) (i : Fin 4) (u : L i) :
      (f.1 ⟨u.1, hL i u.2⟩).1 ∈ R i := by
    rw [← f.2.2 i]
    exact Finset.mem_image.mpr ⟨u, Finset.mem_attach _ _, rfl⟩
  let restrict (f : Q) (i : Fin 4) : L i → R i :=
    fun u => ⟨(f.1 ⟨u.1, hL i u.2⟩).1, hmaps f i u⟩
  have hperfect (f : Q) (i : Fin 4) :
      PerfectMatching G (L i) (R i) (hUW.mono (hL i) (hR i)) (restrict f i) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a b hab
      apply Subtype.ext
      have heq : f.1 ⟨a.1, hL i a.2⟩ = f.1 ⟨b.1, hL i b.2⟩ :=
        Subtype.ext (congrArg (fun v : R i => v.1) hab)
      exact congrArg (fun u : U => u.1) (f.2.1.1.1 heq)
    · intro b
      have hb := b.2
      have hb' : b.1 ∈ ((L i).attach.image fun u =>
          (f.1 ⟨u.1, hL i u.2⟩).1) := by
        simpa only [f.2.2 i] using hb
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb'
      exact ⟨a, Subtype.ext ha⟩
    · intro u
      exact f.2.1.2 ⟨u.1, hL i u.2⟩
  let encode : Q → ∀ i, P i := fun f i => ⟨restrict f i, hperfect f i⟩
  have hinj : Function.Injective encode := by
    intro f g hfg
    apply Subtype.ext
    funext u
    obtain ⟨i, hui⟩ := hcover u.1 u.2
    have h := congrArg (fun p : ∀ i, P i => ((p i).1 ⟨u.1, hui⟩).1) hfg
    exact Subtype.ext h
  have hcard := Fintype.card_le_of_injective encode hinj
  change Q.ncard ≤ ∏ i, (P i).ncard
  simp only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_pi] using hcard
