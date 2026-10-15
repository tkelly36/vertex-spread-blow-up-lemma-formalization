import Tablet.Preamble
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

-- [TABLET NODE: DirectedReachabilitySimplePath]
theorem DirectedReachabilitySimplePath {V : Type*} (R : V → V → Prop)
    {a b : V} (hab : Relation.ReflTransGen R a b) (hne : a ≠ b) :
    ∃ (n : ℕ) (p : Fin (n + 1) → V),
      0 < n ∧ Function.Injective p ∧ p 0 = a ∧ p (Fin.last n) = b ∧
      ∀ i : Fin n, R (p i.castSucc) (p i.succ) := by
-- BODY
  classical
  have hs : ∃ l : List V, (a :: l).Nodup ∧ (a :: l).IsChain R ∧
      (a :: l).getLast (List.cons_ne_nil _ _) = b := by
    clear hne
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], by simp, .singleton _, rfl⟩
    | @head c d hcd hdb ih =>
      obtain ⟨l, hnd, hch, hend⟩ := ih
      by_cases hc : c ∈ d :: l
      · obtain ⟨l₁, l₂, he⟩ := List.mem_iff_append.mp hc
        rw [he] at hnd hch
        refine ⟨l₂, ?_, hch.right_of_append, ?_⟩
        · exact (List.nodup_append.mp hnd).2.1
        · simpa only [he, List.getLast_append_of_right_ne_nil _ _
            (List.cons_ne_nil _ _)] using hend
      · exact ⟨d :: l, List.nodup_cons.mpr ⟨hc, hnd⟩,
          .cons_cons hcd hch, by simpa using hend⟩
  obtain ⟨l, hnd, hch, hend⟩ := hs
  have hpos : 0 < l.length := by
    by_contra h
    have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst l
    exact hne hend
  let p : Fin (l.length + 1) → V := fun i => (a :: l).get
    ⟨i.val, by simpa using i.isLt⟩
  refine ⟨l.length, p, hpos, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have he := (List.nodup_iff_injective_get.mp hnd) hij
    exact Fin.ext (congrArg Fin.val he)
  · rfl
  · simpa [p, List.get_eq_getElem, List.getLast_eq_getElem] using hend
  · intro i
    exact (List.isChain_iff_getElem.mp hch) i.val (by simpa using i.isLt)
