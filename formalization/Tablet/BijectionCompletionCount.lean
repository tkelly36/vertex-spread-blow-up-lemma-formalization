import Tablet.Preamble
import Mathlib.Data.Fintype.Perm

-- [TABLET NODE: BijectionCompletionCount]
theorem BijectionCompletionCount {A B : Type*} [Fintype A] [Fintype B]
    (n s : ℕ) (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (x : Fin s → A) (y : Fin s → B) (hx : Function.Injective x) :
    {f : A → B | Function.Bijective f ∧ ∀ i, f (x i) = y i}.ncard ≤
      (n - s).factorial := by
-- BODY
  classical
  let E := {f : A → B | Function.Bijective f ∧ ∀ i, f (x i) = y i}
  by_cases hE : E.Nonempty
  · obtain ⟨f₀, hf₀, hp₀⟩ := hE
    have hy : Function.Injective y := by
      intro i j hij
      apply hx
      apply hf₀.1
      rw [hp₀ i, hp₀ j, hij]
    let L := {a : A // a ∉ Set.range x}
    let R := {b : B // b ∉ Set.range y}
    have hL : Fintype.card L = n - s := by
      dsimp [L]
      rw [Fintype.card_subtype_compl,
        ← Fintype.card_congr (Equiv.ofInjective x hx), Fintype.card_fin, hA]
    have hR : Fintype.card R = n - s := by
      dsimp [R]
      rw [Fintype.card_subtype_compl,
        ← Fintype.card_congr (Equiv.ofInjective y hy), Fintype.card_fin, hB]
    have hmap (f : E) (a : L) : f.1 a.1 ∉ Set.range y := by
      rintro ⟨i, hi⟩
      apply a.2
      refine ⟨i, ?_⟩
      apply f.2.1.1
      exact (f.2.2 i).trans hi
    let restrict (f : E) : L → R := fun a => ⟨f.1 a.1, hmap f a⟩
    have hbij (f : E) : Function.Bijective (restrict f) := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact f.2.1.1 (congrArg Subtype.val hab)
      · intro b
        obtain ⟨a, ha⟩ := f.2.1.2 b.1
        have hnot : a ∉ Set.range x := by
          rintro ⟨i, rfl⟩
          apply b.2
          exact ⟨i, (f.2.2 i).symm.trans ha⟩
        exact ⟨⟨a, hnot⟩, Subtype.ext ha⟩
    let encode : E → (L ≃ R) := fun f => Equiv.ofBijective (restrict f) (hbij f)
    have hi : Function.Injective encode := by
      intro f g hfg
      apply Subtype.ext
      funext a
      by_cases ha : a ∈ Set.range x
      · obtain ⟨i, rfl⟩ := ha
        exact (f.2.2 i).trans (g.2.2 i).symm
      · exact congrArg (fun e : L ≃ R => (e ⟨a, ha⟩).1) hfg
    have hc := Fintype.card_le_of_injective encode hi
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (hL.trans hR.symm)), hL] at hc
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hc
  · have he : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    change E.ncard ≤ _
    rw [he, Set.ncard_empty]
    exact Nat.zero_le _
