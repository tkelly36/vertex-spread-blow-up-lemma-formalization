import Tablet.SuperRegularSpanningFactor
import Tablet.RegularBipartiteMatchingCount
import Tablet.SuperRegularPair
import Tablet.PerfectMatching

-- [TABLET NODE: MatchingEnumeration]
theorem MatchingEnumeration :
    ∀ ε d : ENNReal, 0 < ε → 2 * ε < d → d ≤ 1 →
      ∃ n₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
        (hUW : Disjoint U W) (n : ℕ),
        n₀ ≤ n → U.card = n → W.card = n → SuperRegularPair G U W ε d →
        (d - 2 * ε) ^ n * (n.factorial : ENNReal) ≤
          ({f : U → W | PerfectMatching G U W hUW f}.ncard : ENNReal) := by
-- BODY
  classical
  intro ε d hε hεd hd
  obtain ⟨n₀, hfactor⟩ := SuperRegularSpanningFactor ε d hε hεd hd
  refine ⟨max n₀ 1, ?_⟩
  intro V _ _ G _ U W hUW n hn hU hW hregular
  have hn₀ : n₀ ≤ n := (le_max_left n₀ 1).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    ((le_max_right n₀ 1).trans hn)
  obtain ⟨k, F, hFG, hk, hleft, hright⟩ :=
    hfactor G U W hUW n hn₀ hU hW hregular
  letI : DecidableRel F.Adj := Classical.decRel _
  have hleft' : ∀ u ∈ U, (W.filter fun w => F.Adj u w).card = k := by
    intro u hu
    have hset : {w | w ∈ W ∧ F.Adj u w} =
        (↑(W.filter fun w => F.Adj u w) : Set V) := by
      ext w
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    simpa only [hset, Set.ncard_coe_finset] using hleft u hu
  have hright' : ∀ w ∈ W, (U.filter fun u => F.Adj u w).card = k := by
    intro w hw
    have hset : {u | u ∈ U ∧ F.Adj u w} =
        (↑(U.filter fun u => F.Adj u w) : Set V) := by
      ext u
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    simpa only [hset, Set.ncard_coe_finset] using hright w hw
  have hnzero : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hratio : d - 2 * ε ≤ (k : ENNReal) / (n : ENNReal) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hnzero)
      (Or.inl (ENNReal.natCast_ne_top n))).2 hk
  have hsubset : {f : U → W | PerfectMatching F U W hUW f} ⊆
      {f : U → W | PerfectMatching G U W hUW f} := by
    intro f hf
    exact ⟨hf.1, fun u => hFG (hf.2 u)⟩
  calc
    (d - 2 * ε) ^ n * (n.factorial : ENNReal) ≤
        ((k : ENNReal) / (n : ENNReal)) ^ n * (n.factorial : ENNReal) :=
      mul_le_mul_right' (pow_le_pow_left' hratio n) _
    _ ≤ ({f : U → W | PerfectMatching F U W hUW f}.ncard : ENNReal) :=
      RegularBipartiteMatchingCount F U W hUW n k hU hW hleft' hright'
    _ ≤ ({f : U → W | PerfectMatching G U W hUW f}.ncard : ENNReal) := by
      exact_mod_cast Set.ncard_mono hsubset
