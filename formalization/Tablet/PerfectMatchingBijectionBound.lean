import Tablet.PerfectMatching
import Mathlib.Data.Fintype.Perm

-- [TABLET NODE: PerfectMatchingBijectionBound]
theorem PerfectMatchingBijectionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (y : ℕ)
    (hA : A.card = y) (hB : B.card = y) :
    {f : A → B | PerfectMatching G A B hAB f}.ncard ≤ y.factorial := by
-- BODY
  classical
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using hA.trans hB.symm)
  let encode : {f : A → B // PerfectMatching G A B hAB f} → (A ≃ B) :=
    fun f => Equiv.ofBijective f.1 f.2.1
  have hi : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun e : A ≃ B => e.toFun) h
  have hc := Fintype.card_le_of_injective encode hi
  rw [Fintype.card_equiv e, Fintype.card_coe, hA] at hc
  simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hc
