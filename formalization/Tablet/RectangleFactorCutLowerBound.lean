import Tablet.Preamble

-- [TABLET NODE: RectangleFactorCutLowerBound]
theorem RectangleFactorCutLowerBound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (k : ℕ)
    (hsize : U.card = W.card)
    (hrect : ∀ X ⊆ U, ∀ Y ⊆ W,
      k * (X.card + Y.card - U.card) ≤
        ((X ×ˢ Y).filter fun p => G.Adj p.1 p.2).card)
    (A B : Finset V) (hA : A ⊆ U) (hB : B ⊆ W) :
    k * U.card ≤ k * A.card +
      (((U \ A) ×ˢ (W \ B)).filter fun p => G.Adj p.1 p.2).card + k * B.card := by
-- BODY
  have ha := Finset.card_le_card hA
  have hb := Finset.card_le_card hB
  have h := hrect (U \ A) Finset.sdiff_subset (W \ B) Finset.sdiff_subset
  rw [Finset.card_sdiff_of_subset hA, Finset.card_sdiff_of_subset hB, ← hsize] at h
  by_cases hab : A.card + B.card ≤ U.card
  · have hd : U.card - A.card + (U.card - B.card) - U.card =
        U.card - (A.card + B.card) := by omega
    rw [hd] at h
    have he : U.card = A.card + B.card + (U.card - (A.card + B.card)) := by omega
    have hm := congrArg (fun x : ℕ => k * x) he
    simp only [Nat.mul_add] at hm
    omega
  · have hle : U.card ≤ A.card + B.card := by omega
    have hm := Nat.mul_le_mul_left k hle
    rw [Nat.mul_add] at hm
    omega
