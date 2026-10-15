import Tablet.Preamble

-- [TABLET NODE: IndependentRetentionCount]
def IndependentRetentionCount {ι : Type*} (I : Finset ι) (ω : ι → Bool) : ℕ :=
-- BODY
  (I.filter fun i => ω i = true).card
