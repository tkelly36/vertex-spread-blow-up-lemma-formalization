import Tablet.Preamble
import Mathlib.Logic.Equiv.Fintype

-- [TABLET NODE: FinitePartialMatchingCompletion]
theorem FinitePartialMatchingCompletion
    {S T : Type*} [Fintype S] [Fintype T] (M : S → T → Prop)
    (hleft : ∀ x y z, M x y → M x z → y = z)
    (hright : ∀ x y z, M x z → M y z → x = y)
    (hcard : Fintype.card S ≤ Fintype.card T) :
    ∃ τ : S ↪ T, ∀ x y, M x y → τ x = y := by
-- BODY
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let A := {x : S // ∃ y, M x y}
  let g : A → T := fun x => Classical.choose x.property
  have hg (x : A) : M x.val (g x) := Classical.choose_spec x.property
  have hginj : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact hright x.val y.val (g y) (h ▸ hg x) (hg y)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x : A => e x.val) g (e.injective.comp Subtype.val_injective) hginj
  refine ⟨e.trans σ.toEmbedding, ?_⟩
  intro x y hxy
  have h := hσ ⟨x, ⟨y, hxy⟩⟩
  change σ (e x) = y
  exact h.trans (hleft x _ y (hg ⟨x, ⟨y, hxy⟩⟩) hxy)
