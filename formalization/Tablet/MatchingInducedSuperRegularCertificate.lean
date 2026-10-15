import Tablet.MatchingInducedGraphIdentities
import Tablet.NearEqualRegularTriplet
import Tablet.NearEqualDegreeCodegreeRegularityCriterion

-- [TABLET NODE: MatchingInducedSuperRegularCertificate]
theorem MatchingInducedSuperRegularCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G F H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] [DecidableRel H.Adj]
    (U W Z : Finset V) (m : ℕ) (ε d x y δ η : ENNReal)
    (hUW : Disjoint U W)
    (ht : NearEqualRegularTriplet G F H U W Z m ε d x y)
    (f : U → W) (hf : PerfectMatching G U W hUW f)
    (hm : 2 ≤ m) (hεη : ε ≤ η) (hεδ : ε ≤ δ)
    (hδη : δ ≤ η) (hδp : δ ≤ x * y) (hp : x * y ≤ 1)
    (hη : η ≤ 1) (hδm : 1 ≤ δ * m) (hhier : 32 * δ ≤ η ^ 5) :
    let A := MatchingInducedGraph F H U W Z f
    letI : DecidableRel A.Adj := Classical.decRel _
    let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
    let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
    (∀ z : Z,
      (x * y - δ) * m ≤ ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ∧
      ((L.filter fun u => A.Adj u (Sum.inr z)).card : ENNReal) ≤ (x * y + δ) * m) →
    (((R ×ˢ R).filter fun z =>
      (x * y + δ) ^ 2 * m <
        ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)).card : ENNReal)
      ≤ 6 * ε * (Z.card : ENNReal) ^ 2 →
    SuperRegularPair A L R η (x * y) := by
-- BODY
  classical
  dsimp only
  intro hdeg hcodeg
  let A := MatchingInducedGraph F H U W Z f
  letI : DecidableRel A.Adj := Classical.decRel _
  let L : Finset (U ⊕ Z) := Finset.univ.image Sum.inl
  let R : Finset (U ⊕ Z) := Finset.univ.image Sum.inr
  obtain ⟨hL, hR, hLR, _, hleft, _, _⟩ := MatchingInducedGraphIdentities F H U W Z f
  change L.card = U.card at hL
  change R.card = Z.card at hR
  obtain ⟨hU, hW, hZ, _, _, _, _, _, _, htrip⟩ := ht
  have hLm : L.card = m := hL.trans hU
  have hRm : R.card + 1 = m ∨ R.card = m ∨ R.card = m + 1 := by
    rw [hR]
    exact hZ
  have hright : ∀ z ∈ R,
      (x * y - δ) * m ≤ ((L.filter fun u => A.Adj u z).card : ENNReal) ∧
      ((L.filter fun u => A.Adj u z).card : ENNReal) ≤ (x * y + δ) * m := by
    intro z hz
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hz
    exact hdeg z
  have hbad : (((R ×ˢ R).filter fun z =>
        ((L.filter fun u => A.Adj u z.1).card : ENNReal) < (x * y - δ) * m ∨
        ((L.filter fun u => A.Adj u z.2).card : ENNReal) < (x * y - δ) * m ∨
        (x * y + δ) ^ 2 * m <
          ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)).card : ENNReal)
        ≤ 6 * δ * (R.card : ENNReal) ^ 2 := by
    have heq : ((R ×ˢ R).filter fun z =>
        ((L.filter fun u => A.Adj u z.1).card : ENNReal) < (x * y - δ) * m ∨
        ((L.filter fun u => A.Adj u z.2).card : ENNReal) < (x * y - δ) * m ∨
        (x * y + δ) ^ 2 * m <
          ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)) =
      ((R ×ˢ R).filter fun z => (x * y + δ) ^ 2 * m <
        ((L.filter fun u => A.Adj u z.1 ∧ A.Adj u z.2).card : ENNReal)) := by
      apply Finset.filter_congr
      intro z hz
      have h₁ := (hright z.1 (Finset.mem_product.mp hz).1).1
      have h₂ := (hright z.2 (Finset.mem_product.mp hz).2).1
      simp only [not_lt_of_ge h₁, not_lt_of_ge h₂, false_or]
    rw [heq, hR]
    exact hcodeg.trans (by gcongr)
  change SuperRegularPair A L R η (x * y)
  refine ⟨NearEqualDegreeCodegreeRegularityCriterion A L R m δ (x * y) η
      hLm hRm hLR hη hδp hp hm hδm hhier hbad, ?_, ?_⟩
  · intro u hu
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hu
    have hrow := htrip u u.property (f u) (f u).property (hf.2 u)
    rw [hleft u, hR]
    constructor
    · exact (mul_le_mul_right' (tsub_le_tsub_left hεη _) _).trans hrow.1
    · exact hrow.2.trans (by gcongr)
  · intro z hz
    rw [hLm]
    have hrow := hright z hz
    constructor
    · exact (mul_le_mul_right' (tsub_le_tsub_left hδη _) _).trans hrow.1
    · exact hrow.2.trans (by gcongr)
