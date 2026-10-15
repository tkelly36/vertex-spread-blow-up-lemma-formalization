import Tablet.Preamble
import Mathlib.Logic.Equiv.Fintype

open scoped symmDiff

-- [TABLET NODE: CapacityPreservingReassignment]
theorem CapacityPreservingReassignment {V J : Type*}
    [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]
    (S E : Finset V) (hES : E ⊆ S) (f b : V → J)
    (hroom : ∀ j, E.card < (S.filter fun v => f v = j).card) :
    ∃ f' : V → J,
      (∀ v ∉ S, f' v = f v) ∧
      (∀ v ∈ E, f' v = b v) ∧
      (∀ j, (S.filter fun v => f' v = j).card =
        (S.filter fun v => f v = j).card) ∧
      (∀ j, ((S.filter fun v => f' v = j) ∆
        (S.filter fun v => f v = j)).card ≤ 2 * E.card) := by
-- BODY
  classical
  let X (j : J) := {v : E // b v.val = j}
  let Y (j : J) := {v : S // f v.val = j}
  have hX (j : J) : Fintype.card (X j) ≤ E.card := by
    calc
      Fintype.card (X j) ≤ Fintype.card E :=
        Fintype.card_le_of_injective (fun v : X j => v.val) Subtype.val_injective
      _ = E.card := Fintype.card_coe E
  have hY (j : J) : Fintype.card (Y j) = (S.filter fun v => f v = j).card := by
    let e : Y j ≃ {v // v ∈ S.filter fun v => f v = j} :=
      { toFun := fun v => ⟨v.val.val, Finset.mem_filter.mpr ⟨v.val.property, v.property⟩⟩
        invFun := fun v => ⟨⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
          (Finset.mem_filter.mp v.property).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  have hslots (j : J) : Nonempty (X j ↪ Y j) :=
    Function.Embedding.nonempty_of_card_le
      ((hX j).trans ((hroom j).le.trans_eq (hY j).symm))
  let slots (j : J) : X j ↪ Y j := (hslots j).some
  -- Assemble the binwise slot injections without choosing a default bin.
  let g : E ↪ S :=
    (((Equiv.sigmaFiberEquiv (fun v : E => b v.val)).symm.toEmbedding).trans
      (Function.Embedding.sigmaMap (Function.Embedding.refl J) slots)).trans
      (Equiv.sigmaFiberEquiv (fun v : S => f v.val)).toEmbedding
  have hglabel (v : E) : f (g v).val = b v.val :=
    (slots (b v.val) ⟨v, rfl⟩).property
  have hginj : Function.Injective g := g.injective
  let H : Finset V := Finset.univ.image (fun v : E => (g v).val)
  let T : Finset V := E ∪ H
  have hgT (v : E) : (g v).val ∈ T :=
    Finset.mem_union_right E (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  have hTS : T ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hES hv
    · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact (g w).property
  have hTcard : T.card ≤ 2 * E.card := by
    have hH : H.card ≤ E.card := by
      exact Finset.card_image_le.trans (by simp)
    exact (Finset.card_union_le E H).trans (by omega)
  let i : E → T := fun v => ⟨v.val, Finset.mem_union_left H v.property⟩
  let k : E → T := fun v => ⟨(g v).val, hgT v⟩
  have hi : Function.Injective i := by
    intro v w h
    exact Subtype.ext (congrArg (fun z : T => z.val) h)
  have hk : Function.Injective k := by
    intro v w h
    apply hginj
    exact Subtype.ext (congrArg (fun z : T => z.val) h)
  -- Complete only inside T; an arbitrary permutation of V would lose the bound.
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair i k hi hk
  let π : Equiv.Perm V := σ.extendDomain (Equiv.refl T)
  have hfix (v : V) (hv : v ∉ T) : π v = v :=
    Equiv.Perm.extendDomain_apply_not_subtype σ (Equiv.refl T) hv
  have hinside (v : V) (hv : v ∈ T) : π v ∈ T := by
    rw [Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl T) hv]
    exact (σ ⟨v, hv⟩).property
  have hS (v : V) : π v ∈ S ↔ v ∈ S := by
    by_cases hv : v ∈ T
    · exact iff_of_true (hTS (hinside v hv)) (hTS hv)
    · rw [hfix v hv]
  have hprescribed (v : E) : π v.val = (g v).val := by
    have h := congrArg Subtype.val (hσ v)
    simpa only [π, Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl T)
      (Finset.mem_union_left H v.property), Equiv.refl_apply, Equiv.refl_symm, i, k] using h
  refine ⟨fun v => f (π v), ?_, ?_, ?_, ?_⟩
  · intro v hv
    change f (π v) = f v
    rw [hfix v (fun h => hv (hTS h))]
  · intro v hv
    change f (π v) = b v
    rw [hprescribed ⟨v, hv⟩]
    exact hglabel ⟨v, hv⟩
  · intro j
    apply Finset.card_bij (fun v _ => π v)
    · intro v hv
      exact Finset.mem_filter.mpr ⟨(hS v).mpr (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩
    · intro v _ w _ h
      exact π.injective h
    · intro w hw
      refine ⟨π.symm w, ?_, π.apply_symm_apply w⟩
      apply Finset.mem_filter.mpr
      exact ⟨(hS (π.symm w)).mp (by simpa only [π.apply_symm_apply] using
        (Finset.mem_filter.mp hw).1), by simpa only [π.apply_symm_apply] using
        (Finset.mem_filter.mp hw).2⟩
  · intro j
    -- Every bin changes only on the same explicitly bounded support T.
    apply (Finset.card_le_card ?_).trans hTcard
    intro v hv
    by_contra hn
    have heq : (v ∈ S.filter fun v => f (π v) = j) ↔
        (v ∈ S.filter fun v => f v = j) := by
      simp only [Finset.mem_filter, hfix v hn]
    simpa only [Finset.mem_symmDiff, heq, not_and_self, and_not_self, or_self] using hv
