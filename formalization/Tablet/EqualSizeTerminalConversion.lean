import Tablet.PartialCompatibleEmbedding
import Tablet.VertexSpreadOn
import Tablet.VertexSpreadRestriction

-- [TABLET NODE: EqualSizeTerminalConversion]
theorem EqualSizeTerminalConversion
    {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (X : Finset VH) (μ : PMF (PartialCompatibleEmbedding B A X))
    (b : ENNReal) (hX : X = Finset.univ)
    (hspread : VertexSpreadOn
      (μ.map fun f => fun x : {x : VH // x ∈ X} => f.toFun x.1) b Set.univ) :
    ∃ F : PartialCompatibleEmbedding B A X →
        {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ},
      (∀ f x, (F f).1 x = f.toFun x) ∧
      VertexSpreadOn ((μ.map F).map fun φ => fun x => φ.1 x) b Set.univ := by
-- BODY
  have hx : ∀ x : VH, x ∈ X := by
    intro x
    rw [hX]
    exact Finset.mem_univ x
  let F : PartialCompatibleEmbedding B A X →
      {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ} := fun f =>
    ⟨{ toHom :=
         { toFun := f.toFun
           map_rel' := fun {x y} hxy => f.map_adj (hx x) (hx y) hxy }
       injective' := fun x y hxy => f.injOn (hx x) (hx y) hxy },
     fun x => f.compatible x (hx x)⟩
  have hF : ∀ f x, (F f).1 x = f.toFun x := fun _ _ => rfl
  refine ⟨F, hF, ?_⟩
  let e : VH ↪ {x : VH // x ∈ X} :=
    ⟨fun x => ⟨x, hx x⟩, fun _ _ h => congrArg Subtype.val h⟩
  have hfull := VertexSpreadRestriction e hspread
  rw [PMF.map_comp] at hfull
  rw [PMF.map_comp]
  exact hfull
