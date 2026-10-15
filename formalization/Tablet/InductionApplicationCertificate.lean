import Tablet.NearEqualFourGraphs
import Tablet.UniformPerfectMatchingSpread
import Tablet.QuantitativeSuperRegularThinning
import Tablet.MatchingEnumeration

-- [TABLET NODE: InductionApplicationCertificate]
structure InductionApplicationCertificate
    (Delta Q : ℕ) (d : ENNReal)
    (t D beta rho eta omega xi : ℕ → ENNReal) where
-- BODY
  witnessThinningThreshold : ℕ → ℕ → ℕ
  hostThinningThreshold : ℕ → ℕ
  fourGraphsConstant : ℕ → ℕ → ℕ → ENNReal
  fourGraphsThreshold : ℕ → ℕ → ℕ → ℕ
  matchingConstant : ℕ → ℕ → ENNReal
  matchingThreshold : ℕ → ℕ → ℕ
  matchingExistenceThreshold : ℕ → ℕ → ℕ
  witnessThinningGuarantee : ∀ round, round < Q → ∀ x, x ≤ Delta →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V),
      Disjoint L R → witnessThinningThreshold round x ≤ L.card →
      witnessThinningThreshold round x ≤ R.card → L.card ≤ R.card + 1 → R.card ≤ L.card + 1 →
      SuperRegularPair G L R (beta round) (D x) →
      ∃ G' : SimpleGraph V, G' ≤ G ∧
        @SuperRegularPair V _ G' (Classical.decRel _) L R (xi round) (rho x)
  hostThinningGuarantee : ∀ round, round < Q →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V),
      Disjoint L R → hostThinningThreshold round ≤ L.card →
      hostThinningThreshold round ≤ R.card → L.card ≤ R.card + 1 → R.card ≤ L.card + 1 →
      SuperRegularPair G L R (beta 0) d →
      ∃ G' : SimpleGraph V, G' ≤ G ∧
        @SuperRegularPair V _ G' (Classical.decRel _) L R (xi round) (d / 2)
  fourGraphsPositive : ∀ round, round < Q → ∀ xCurrent xFuture,
    xCurrent ≤ Delta → xFuture ≤ Delta →
    0 < fourGraphsConstant round xCurrent xFuture ∧
      fourGraphsConstant round xCurrent xFuture ≤ 1
  fourGraphsGuarantee : ∀ round, round < Q → ∀ xCurrent xFuture,
    xCurrent ≤ Delta → xFuture ≤ Delta →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (F₁₂ F₁₃ F₂₃ : SimpleGraph V)
      [DecidableRel F₁₂.Adj] [DecidableRel F₁₃.Adj] [DecidableRel F₂₃.Adj]
      (W₁ W₂ W₃ : Finset V) (m : ℕ),
      fourGraphsThreshold round xCurrent xFuture ≤ m →
      NearEqualRegularTriplet F₁₂ F₁₃ F₂₃ W₁ W₂ W₃ m
        (t round) (rho xCurrent) (rho xFuture) (d / 2) →
      ∀ (h₁₂ : Disjoint W₁ W₂)
        (hM : Nonempty {σ : W₁ → W₂ // PerfectMatching F₁₂ W₁ W₂ h₁₂ σ}),
        let μ := UniformPerfectMatching F₁₂ W₁ W₂ h₁₂ hM
        let L : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inl
        let R : Finset (W₁ ⊕ W₃) := Finset.univ.image Sum.inr
        1 - (1 - fourGraphsConstant round xCurrent xFuture) ^ m ≤
          μ.toOuterMeasure {σ |
            letI : DecidableRel
                (MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ σ).Adj := Classical.decRel _
            SuperRegularPair
              (MatchingInducedGraph F₁₃ F₂₃ W₁ W₂ W₃ σ)
              L R (omega (round + 1)) (rho xFuture * (d / 2))}
  matchingConstantAtLeastOne : ∀ round, round < Q → ∀ x, x ≤ Delta →
    1 ≤ matchingConstant round x
  matchingExistenceGuarantee : ∀ round, round < Q → ∀ x, x ≤ Delta →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (hUW : Disjoint U W) (m : ℕ),
      matchingExistenceThreshold round x ≤ m → U.card = m → W.card = m →
      SuperRegularPair G U W (t round) (rho x) →
      Nonempty {f : U → W // PerfectMatching G U W hUW f}
  matchingGuarantee : ∀ round, round < Q → ∀ x, x ≤ Delta →
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (U W : Finset V) (hUW : Disjoint U W) (m : ℕ),
      matchingThreshold round x ≤ m → U.card = m → W.card = m →
      SuperRegularPair G U W (t round) (rho x) →
      ∀ h : Nonempty {f : U → W // PerfectMatching G U W hUW f},
        VertexSpreadOn
          ((UniformPerfectMatching G U W hUW h).map fun f u => (f.val u : V))
          (matchingConstant round x / m) Set.univ
