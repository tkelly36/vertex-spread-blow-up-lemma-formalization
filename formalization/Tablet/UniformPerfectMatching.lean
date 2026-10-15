import Tablet.PerfectMatching

-- [TABLET NODE: UniformPerfectMatching]
noncomputable def UniformPerfectMatching {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (hUW : Disjoint U W)
    (h : Nonempty {f : U → W // PerfectMatching G U W hUW f}) :
    PMF {f : U → W // PerfectMatching G U W hUW f} := by
-- BODY
  classical
  letI := h
  exact PMF.uniformOfFintype {f : U → W // PerfectMatching G U W hUW f}
