import Tablet.SuperRegularPair

-- [TABLET NODE: SuperRegularErrorMonotone]
theorem SuperRegularErrorMonotone {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L R : Finset V)
    (beta gamma d : ENNReal) (h : beta ≤ gamma) :
    SuperRegularPair G L R beta d → SuperRegularPair G L R gamma d := by
-- BODY
  rintro ⟨hreg, hleft, hright⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U hU W hW hUL hWR
    obtain ⟨hlo, hhi⟩ := hreg U hU W hW
      (lt_of_le_of_lt (mul_le_mul_left h _) hUL)
      (lt_of_le_of_lt (mul_le_mul_left h _) hWR)
    exact ⟨(tsub_le_tsub_left h d).trans hlo, hhi.trans (add_le_add le_rfl h)⟩
  · intro v hv
    obtain ⟨hlo, hhi⟩ := hleft v hv
    exact ⟨(mul_le_mul_left (tsub_le_tsub_left h d) _).trans hlo,
      hhi.trans (mul_le_mul_left (add_le_add le_rfl h) _)⟩
  · intro w hw
    obtain ⟨hlo, hhi⟩ := hright w hw
    exact ⟨(mul_le_mul_left (tsub_le_tsub_left h d) _).trans hlo,
      hhi.trans (mul_le_mul_left (add_le_add le_rfl h) _)⟩
