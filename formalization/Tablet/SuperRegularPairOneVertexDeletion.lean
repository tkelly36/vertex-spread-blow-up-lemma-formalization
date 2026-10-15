import Tablet.SuperRegularPair

-- [TABLET NODE: SuperRegularPairOneVertexDeletion]
theorem SuperRegularPairOneVertexDeletion
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L R A B : Finset V) (m : ℕ) (τ η c : ℝ)
    (hτ : 0 ≤ τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hsmall : 4 * τ ≤ η)
    (hm : 1 ≤ m) (hfloor : 4 ≤ η * m)
    (hAL : A ⊆ L) (hBR : B ⊆ R)
    (hA : m ≤ A.card) (hB : m ≤ B.card)
    (hLA : L.card ≤ A.card + 1) (hRB : R.card ≤ B.card + 1)
    (hG : SuperRegularPair G L R (ENNReal.ofReal τ) (ENNReal.ofReal c)) :
    SuperRegularPair G A B (ENNReal.ofReal η) (ENNReal.ofReal c) := by
-- BODY
  classical
  have hτη : τ ≤ η := by linarith
  have hτ1 : τ ≤ 1 := by linarith
  have threshold (S T : Finset V) (hT : m ≤ T.card)
      (hST : S.card ≤ T.card + 1) :
      ENNReal.ofReal τ * (S.card : ENNReal) ≤
        ENNReal.ofReal η * (T.card : ENNReal) := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ,
      ENNReal.toReal_ofReal hη.le, ENNReal.toReal_natCast]
    have ht : (1 : ℝ) ≤ T.card := by exact_mod_cast (hm.trans hT)
    have hs : (S.card : ℝ) ≤ T.card + 1 := by exact_mod_cast hST
    nlinarith only [hτ, hsmall, hη.le, hs, ht,
      mul_nonneg (sub_nonneg.mpr hτη) (sub_nonneg.mpr ht)]
  have degree (S T : Finset V) (p : V → Prop) [DecidablePred p]
      (hTS : T ⊆ S) (hT : m ≤ T.card) (hST : S.card ≤ T.card + 1)
      (hold : (ENNReal.ofReal c - ENNReal.ofReal τ) * (S.card : ENNReal) ≤
          (S.filter p).card ∧
        ((S.filter p).card : ENNReal) ≤
          (ENNReal.ofReal c + ENNReal.ofReal τ) * (S.card : ENNReal)) :
      (ENNReal.ofReal c - ENNReal.ofReal η) * (T.card : ENNReal) ≤
          (T.filter p).card ∧
        ((T.filter p).card : ENNReal) ≤
          (ENNReal.ofReal c + ENNReal.ofReal η) * (T.card : ENNReal) := by
    have hsd : (S \ T).card ≤ 1 := by
      have := Finset.card_sdiff_add_card_eq_card hTS
      omega
    have sub : S.filter p ⊆ (T.filter p) ∪ (S \ T) := by
      intro x hx
      obtain ⟨hxS, hp⟩ := Finset.mem_filter.mp hx
      by_cases hxT : x ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxT, hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxS, hxT⟩)
    have loss : (S.filter p).card ≤ (T.filter p).card + 1 :=
      (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans (by omega))
    have keep : (T.filter p).card ≤ (S.filter p).card :=
      Finset.card_le_card (Finset.filter_subset_filter p hTS)
    have ks : (T.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hTS
    have sk : (S.card : ℝ) ≤ T.card + 1 := by exact_mod_cast hST
    have tk : (m : ℝ) ≤ T.card := by exact_mod_cast hT
    have kl : ((S.filter p).card : ℝ) ≤ (T.filter p).card + 1 := by exact_mod_cast loss
    have ku : ((T.filter p).card : ℝ) ≤ (S.filter p).card := by exact_mod_cast keep
    have margin : 4 ≤ η * (T.card : ℝ) :=
      hfloor.trans (mul_le_mul_of_nonneg_left tk hη.le)
    have oldupper := ENNReal.toReal_mono (by finiteness) hold.2
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hτ] at oldupper
    have oldlower : (c - τ) * (S.card : ℝ) ≤ (S.filter p).card := by
      by_cases hτc : τ ≤ c
      · have hh := ENNReal.toReal_mono (by simp) hold.1
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hτc) (by finiteness),
          ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hτ] using hh
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans
          (Nat.cast_nonneg _)
    have lower : (c - η) * (T.card : ℝ) ≤ (T.filter p).card := by
      by_cases hηc : η ≤ c
      · have hct : 0 ≤ c - τ := by linarith
        have cross := mul_le_mul_of_nonneg_left ks hct
        have budget := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg T.card : (0 : ℝ) ≤ _)
        nlinarith only [oldlower, kl, cross, margin, budget]
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans
          (Nat.cast_nonneg _)
    have upper : ((T.filter p).card : ℝ) ≤ (c + η) * (T.card : ℝ) := by
      have cross := mul_le_mul_of_nonneg_left sk (add_nonneg hc hτ)
      have budget := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg T.card : (0 : ℝ) ≤ _)
      nlinarith only [oldupper, ku, cross, margin, budget, hc1, hτ1]
    constructor
    · by_cases hηc : η ≤ c
      · apply (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mp
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hηc) (by finiteness),
          ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hη.le] using lower
      · simp [tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal (le_of_not_ge hηc))]
    · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hη.le] using upper
  refine ⟨?_, ?_, ?_⟩
  · intro S hS T hT hsizeS hsizeT
    obtain ⟨hl, hu⟩ := hG.1 S (hS.trans hAL) T (hT.trans hBR)
      ((threshold L A hA hLA).trans_lt hsizeS)
      ((threshold R B hB hRB).trans_lt hsizeT)
    exact ⟨(tsub_le_tsub_left (ENNReal.ofReal_le_ofReal hτη) _).trans hl,
      hu.trans (add_le_add_right (ENNReal.ofReal_le_ofReal hτη) _)⟩
  · intro x hx
    exact degree R B (fun y => G.Adj x y) hBR hB hRB (hG.2.1 x (hAL hx))
  · intro y hy
    exact degree L A (fun x => G.Adj x y) hAL hA hLA (hG.2.2 y (hBR hy))
