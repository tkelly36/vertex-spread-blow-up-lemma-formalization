import Tablet.PairDensity
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.ENNReal.Real

-- [TABLET NODE: PairDensityReal]
theorem PairDensityReal {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    PairDensity G A B ≠ ⊤ ∧
      (PairDensity G A B).toReal = (G.edgeDensity A B : ℝ) ∧
      (G.edgeDensity A B : ℝ) =
        (((A.product B).filter fun e => G.Adj e.1 e.2).card : ℝ) /
          ((A.card : ℝ) * (B.card : ℝ)) := by
-- BODY
  have hden : (A.card : ENNReal) * (B.card : ENNReal) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hA.card_pos.ne')
      (by exact_mod_cast hB.card_pos.ne')
  have hfinite : PairDensity G A B ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp) hden
  have hr : (PairDensity G A B).toReal =
      (((A.product B).filter fun e => G.Adj e.1 e.2).card : ℝ) /
        ((A.card : ℝ) * (B.card : ℝ)) := by
    simp only [PairDensity, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
  have hd : (G.edgeDensity A B : ℝ) =
      (((A.product B).filter fun e => G.Adj e.1 e.2).card : ℝ) /
        ((A.card : ℝ) * (B.card : ℝ)) := by
    simp [SimpleGraph.edgeDensity, Rel.edgeDensity, Rel.interedges]
  exact ⟨hfinite, hr.trans hd.symm, hd⟩
