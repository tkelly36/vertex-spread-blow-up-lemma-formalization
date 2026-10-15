import Tablet.Preamble
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- [TABLET NODE: FourRectangleFactorialCancellation]
theorem FourRectangleFactorialCancellation (n s t x : ℕ)
    (hs : s ≤ n) (ht : t ≤ n) (hxs : x ≤ s) (hxt : x ≤ t)
    (hfit : t - x ≤ n - s) :
    (s.choose x : ℝ) * (t.choose x : ℝ) *
      ((n - t).choose (s - x) : ℝ) * ((n - s).choose (t - x) : ℝ) *
      ((x.factorial : ℝ) * ((s - x).factorial : ℝ) *
        ((t - x).factorial : ℝ) * ((n - s - (t - x)).factorial : ℝ)) /
      (n.factorial : ℝ) =
    (t.choose x : ℝ) * ((n - t).choose (s - x) : ℝ) / (n.choose s : ℝ) := by
-- BODY
  have h₁ : (s.choose x : ℝ) * (x.factorial : ℝ) *
      ((s - x).factorial : ℝ) = (s.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hxs
  have h₂ : ((n - s).choose (t - x) : ℝ) * ((t - x).factorial : ℝ) *
      ((n - s - (t - x)).factorial : ℝ) = ((n - s).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hfit
  have h₃ : (n.choose s : ℝ) * (s.factorial : ℝ) *
      ((n - s).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
  have hn : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hc : (n.choose s : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hs
  apply (div_eq_div_iff hn hc).2
  calc
    _ = (t.choose x : ℝ) * ((n - t).choose (s - x) : ℝ) *
        ((n.choose s : ℝ) *
          ((s.choose x : ℝ) * (x.factorial : ℝ) * ((s - x).factorial : ℝ)) *
          (((n - s).choose (t - x) : ℝ) * ((t - x).factorial : ℝ) *
            ((n - s - (t - x)).factorial : ℝ))) := by ring
    _ = _ := by rw [h₁, h₂, h₃]
