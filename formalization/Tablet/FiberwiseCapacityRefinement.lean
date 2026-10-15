import Tablet.Preamble

-- [TABLET NODE: FiberwiseCapacityRefinement]
theorem FiberwiseCapacityRefinement
    {I J X V : Type*} [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq J]
    (a : X → I) (b : V → I) (c : X → J) (j₀ : J)
    (e : ∀ i, {x : X // a x = i} ↪ {v : V // b v = i}) :
    ∃ d : V → J, ∀ i j,
      Fintype.card {x : X // a x = i ∧ c x = j} ≤
        Fintype.card {v : V // b v = i ∧ d v = j} := by
-- BODY
  classical
  let f : X → V := fun x => (e (a x) ⟨x, rfl⟩).val
  have hf (x : X) : b (f x) = a x := (e (a x) ⟨x, rfl⟩).property
  have hfiber (x : X) (i : I) (h : a x = i) :
      f x = (e i ⟨x, h⟩).val := by
    subst i
    rfl
  have hfi : Function.Injective f := by
    intro x y h
    have hi : a x = a y := (hf x).symm.trans ((congrArg b h).trans (hf y))
    have hey := hfiber y (a x) hi.symm
    exact congrArg Subtype.val ((e (a x)).injective (Subtype.ext (h.trans hey)))
  let d : V → J := fun v => if h : ∃ x, f x = v then c h.choose else j₀
  have hd (x : X) : d (f x) = c x := by
    dsimp [d]
    rw [dif_pos ⟨x, rfl⟩]
    exact congrArg c (hfi (Classical.choose_spec (show ∃ y, f y = f x from ⟨x, rfl⟩)))
  refine ⟨d, fun i j => Fintype.card_le_of_injective
    (fun x => (⟨f x.val, (hf x.val).trans x.property.1,
      (hd x.val).trans x.property.2⟩ : {v : V // b v = i ∧ d v = j})) ?_⟩
  intro x y h
  exact Subtype.ext (hfi (congrArg Subtype.val h))
