import Tablet.ColourRoundInvariant

-- [TABLET NODE: ColourRoundReset]
theorem ColourRoundReset
    {r q : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel R.Adj]
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (colour : Fin r → Fin q) (epsilon density : ℕ → ENNReal)
    (D : ℕ) (C : ENNReal) (n round : ℕ)
    (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X))
    (hnext : round + 1 < q) (hepsilon : epsilon round ≤ epsilon (round + 1))
    (hμ : ColourRoundInvariant B A colour epsilon density D C n round
      (Finset.univ.filter fun j : Fin r => (colour j).val = round) X μ) :
    ColourRoundInvariant B A colour epsilon density D C n (round + 1) ∅ X μ := by
-- BODY
  classical
  have widen (W : SimpleGraph (VH ⊕ VG))
      (L Q : Finset (VH ⊕ VG)) (a b d : ENNReal) (hab : a ≤ b)
      (hW : @SuperRegularPair (VH ⊕ VG) _ W (Classical.decRel _) L Q a d) :
      @SuperRegularPair (VH ⊕ VG) _ W (Classical.decRel _) L Q b d := by
    rcases hW with ⟨hreg, hleft, hright⟩
    have hlo : d - b ≤ d - a := tsub_le_tsub_left hab d
    have hhi : d + a ≤ d + b := add_le_add le_rfl hab
    refine ⟨?_, ?_, ?_⟩
    · intro U hU V hV hsizeU hsizeV
      obtain ⟨hl, hu⟩ := hreg U hU V hV
        (lt_of_le_of_lt (mul_le_mul_left hab _) hsizeU)
        (lt_of_le_of_lt (mul_le_mul_left hab _) hsizeV)
      exact ⟨hlo.trans hl, hu.trans hhi⟩
    · intro v hv
      obtain ⟨hl, hu⟩ := hleft v hv
      exact ⟨(mul_le_mul_left hlo _).trans hl,
        hu.trans (mul_le_mul_left hhi _)⟩
    · intro v hv
      obtain ⟨hl, hu⟩ := hright v hv
      exact ⟨(mul_le_mul_left hlo _).trans hl,
        hu.trans (mul_le_mul_left hhi _)⟩
  have processed (k : Fin r) :
      ((colour k).val < round ∨ (colour k).val = round) ↔
      (colour k).val < round + 1 := by
    omega
  rcases hμ with ⟨_, hdegree, hcolour, _, hdomain, hspread, hwitness⟩
  refine ⟨hnext, hdegree, hcolour, ?_, ?_, hspread, ?_⟩
  · simp
  · rw [hdomain]
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      or_false]
    exact processed (B.sourceCluster x)
  · intro f hf j _ hj
    have hjold : round ≤ (colour j).val := by omega
    have hjuntouched :
        j ∉ Finset.univ.filter (fun k : Fin r => (colour k).val = round) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hexposure :
        (Finset.univ.filter fun k : Fin r =>
          ((colour k).val < round ∨
            k ∈ Finset.univ.filter (fun l : Fin r => (colour l).val = round)) ∧
          R.Adj j k) =
        (Finset.univ.filter fun k : Fin r =>
          ((colour k).val < round + 1 ∨ k ∈ (∅ : Finset (Fin r))) ∧
          R.Adj j k) := by
      apply Finset.ext
      intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        or_false]
      exact and_congr (processed k) Iff.rfl
    have hold := hwitness f hf j hjuntouched hjold
    dsimp only at hold ⊢
    rw [hexposure] at hold
    rcases hold with ⟨hex, _, W, hW, hreg⟩
    simp only [Finset.filter_empty, Finset.card_empty, Finset.not_nonempty_empty,
      if_false]
    refine ⟨hex, Nat.zero_le 1, W, hW, ?_⟩
    split_ifs at hreg with htouch
    · exact hreg
    · exact widen W _ _ _ _ _ hepsilon hreg
