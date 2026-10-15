import Tablet.Preamble
import Mathlib.Data.Finset.Powerset

-- [TABLET NODE: FourRectangleMatchingPartition]
theorem FourRectangleMatchingPartition
    {V : Type*} [DecidableEq V]
    (U W S T : Finset V) (F : V → V)
    (hF : Set.BijOn F (U : Set V) (W : Set V))
    (hS : S ⊆ U) (hT : T ⊆ W) (n x : ℕ)
    (hU : U.card = n) (hW : W.card = n)
    (hx : (S.filter fun u => F u ∈ T).card = x) :
    let A := S.filter fun u => F u ∈ T
    let B := A.image F
    let C := (S \ A).image F
    let E := U.filter fun u => F u ∈ T \ B
    A ∈ S.powersetCard x ∧ B ∈ T.powersetCard x ∧
    C ∈ (W \ T).powersetCard (S.card - x) ∧
    E ∈ (U \ S).powersetCard (T.card - x) ∧
    E.image F = T \ B ∧
    (U \ (S ∪ E)).image F = W \ (T ∪ C) ∧
    (S \ A).card = S.card - x ∧ (T \ B).card = T.card - x ∧
    (U \ (S ∪ E)).card = n - S.card - (T.card - x) ∧
    (W \ (T ∪ C)).card = n - S.card - (T.card - x) ∧
    A ∪ (S \ A) ∪ E ∪ (U \ (S ∪ E)) = U ∧
    B ∪ C ∪ (T \ B) ∪ (W \ (T ∪ C)) = W := by
-- BODY
  classical
  dsimp only
  let A := S.filter fun u => F u ∈ T
  let B := A.image F
  let C := (S \ A).image F
  let E := U.filter fun u => F u ∈ T \ B
  change A ∈ S.powersetCard x ∧ B ∈ T.powersetCard x ∧
    C ∈ (W \ T).powersetCard (S.card - x) ∧
    E ∈ (U \ S).powersetCard (T.card - x) ∧ _
  have hA : A ⊆ S := Finset.filter_subset _ _
  have hAU : A ⊆ U := hA.trans hS
  have hAc : A.card = x := hx
  have hB : B ⊆ T := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hu).2
  have hBc : B.card = x := by
    rw [show B = A.image F from rfl,
      Finset.card_image_of_injOn (hF.injOn.mono hAU), hAc]
  have hC : C ⊆ W \ T := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨huS, huA⟩ := Finset.mem_sdiff.mp hu
    refine Finset.mem_sdiff.mpr ⟨hF.mapsTo (hS huS), ?_⟩
    intro huT
    exact huA (Finset.mem_filter.mpr ⟨huS, huT⟩)
  have hSc : (S \ A).card = S.card - x := by
    rw [Finset.card_sdiff_of_subset hA, hAc]
  have hCc : C.card = S.card - x := by
    rw [show C = (S \ A).image F from rfl,
      Finset.card_image_of_injOn (hF.injOn.mono (Finset.sdiff_subset.trans hS)), hSc]
  have hEU : E ⊆ U := Finset.filter_subset _ _
  have hE : E ⊆ U \ S := by
    intro u hu
    obtain ⟨huU, huTB⟩ := Finset.mem_filter.mp hu
    obtain ⟨huT, huB⟩ := Finset.mem_sdiff.mp huTB
    refine Finset.mem_sdiff.mpr ⟨huU, ?_⟩
    intro huS
    exact huB (Finset.mem_image.mpr
      ⟨u, Finset.mem_filter.mpr ⟨huS, huT⟩, rfl⟩)
  have hEi : E.image F = T \ B := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hu).2
    · intro hv
      obtain ⟨u, huU, hu⟩ := hF.surjOn (hT (Finset.mem_sdiff.mp hv).1)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huU, hu ▸ hv⟩, hu⟩
  have hTc : (T \ B).card = T.card - x := by
    rw [Finset.card_sdiff_of_subset hB, hBc]
  have hEc : E.card = T.card - x := by
    rw [← Finset.card_image_of_injOn (hF.injOn.mono hEU), hEi, hTc]
  have hSE : Disjoint S E := by
    apply Finset.disjoint_left.mpr
    intro u huS huE
    exact (Finset.mem_sdiff.mp (hE huE)).2 huS
  have hSEU : S ∪ E ⊆ U := Finset.union_subset hS hEU
  have hSU : S.image F = B ∪ C := by
    rw [show B = A.image F from rfl, show C = (S \ A).image F from rfl,
      ← Finset.image_union]
    congr 1
    exact (Finset.union_sdiff_of_subset hA).symm
  have hSEi : (S ∪ E).image F = T ∪ C := by
    rw [Finset.image_union, hSU, hEi]
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have := @hB v
    tauto
  have hUi : U.image F = W := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact hF.mapsTo hu
    · intro hv
      obtain ⟨u, hu, h⟩ := hF.surjOn hv
      exact Finset.mem_image.mpr ⟨u, hu, h⟩
  have hDi : (U \ (S ∪ E)).image F = W \ (T ∪ C) := by
    rw [Finset.image_sdiff_of_injOn hF.injOn hSEU, hUi, hSEi]
  have hDc : (U \ (S ∪ E)).card = n - S.card - (T.card - x) := by
    rw [Finset.card_sdiff_of_subset hSEU, hU,
      Finset.card_union_of_disjoint hSE, hEc, Nat.sub_add_eq]
  have hRc : (W \ (T ∪ C)).card = n - S.card - (T.card - x) := by
    rw [← hDi, Finset.card_image_of_injOn (hF.injOn.mono Finset.sdiff_subset), hDc]
  refine ⟨Finset.mem_powersetCard.mpr ⟨hA, hAc⟩,
    Finset.mem_powersetCard.mpr ⟨hB, hBc⟩,
    Finset.mem_powersetCard.mpr ⟨hC, hCc⟩,
    Finset.mem_powersetCard.mpr ⟨hE, hEc⟩,
    hEi, hDi, hSc, hTc, hDc, hRc, ?_, ?_⟩
  · rw [Finset.union_sdiff_of_subset hA, Finset.union_sdiff_of_subset hSEU]
  · rw [show B ∪ C ∪ (T \ B) = T ∪ C by
      ext v
      simp only [Finset.mem_union, Finset.mem_sdiff]
      have := @hB v
      tauto]
    exact Finset.union_sdiff_of_subset
      (Finset.union_subset hT (hC.trans Finset.sdiff_subset))
