import Tablet.Preamble
import Mathlib.Logic.Equiv.Basic

-- [TABLET NODE: MatchingThreeEdgeSwitch]
def MatchingThreeEdgeSwitch {A B : Type*} [DecidableEq A]
    (f : A → B) (x a b : A) : A → B :=
-- BODY
  fun z => f (Equiv.swap x a (Equiv.swap a b z))
