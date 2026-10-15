import Tablet.Preamble
import Mathlib.Logic.Equiv.Fintype

open scoped BigOperators
open scoped Classical

-- [TABLET NODE: ProductPermutationSubsetLaw]
theorem ProductPermutationSubsetLaw {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → Type*) [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (i : I) (S : Finset (F i)) (P : Finset (F i) → Prop) :
    (((Finset.univ : Finset (∀ j, Equiv.Perm (F j))).filter
      fun (ω : ∀ j, Equiv.Perm (F j)) => P (S.image (ω i))).card : ℝ) /
        (Fintype.card (∀ j, Equiv.Perm (F j)) : ℝ) =
    ((((Finset.univ : Finset (F i)).powersetCard S.card).filter P).card : ℝ) /
      (((Finset.univ : Finset (F i)).powersetCard S.card).card : ℝ) := by
-- BODY
  classical
  let Ω := ∀ j, Equiv.Perm (F j)
  let b (ω : Ω) := S.image (ω i)
  let K := (Finset.univ : Finset (F i)).powersetCard S.card
  let c := ((Finset.univ : Finset Ω).filter fun ω => b ω = S).card
  have hb (ω : Ω) : b ω ∈ K := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, Finset.card_image_of_injective _ (ω i).injective⟩
  have hc : 0 < c := by
    apply Finset.card_pos.mpr
    refine ⟨fun j => Equiv.refl _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [b]
  have hfiber (U : Finset (F i)) (hU : U ∈ K) :
      ((Finset.univ : Finset Ω).filter fun ω => b ω = U).card = c := by
    have hcard : S.card = U.card := (Finset.mem_powersetCard.mp hU).2.symm
    let e : {a // a ∈ S} ≃ {a // a ∈ U} := Finset.equivOfCardEq hcard
    let π := e.extendSubtype
    have hπ (a : F i) : π a ∈ U ↔ a ∈ S := by
      constructor
      · intro h
        by_contra hn
        exact e.extendSubtype_not_mem a hn h
      · exact e.extendSubtype_mem a
    have hπS : S.image π = U := by
      ext a
      constructor
      · rintro ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
        exact (hπ v).mpr hv
      · intro ha
        exact Finset.mem_image.mpr ⟨π.symm a,
          (hπ (π.symm a)).mp (by simpa using ha), π.apply_symm_apply a⟩
    let q : ∀ j, Equiv.Perm (F j) := Function.update (fun j => Equiv.refl (F j)) i π
    let τ : Ω ≃ Ω :=
      { toFun := fun ω j => (ω j).trans (q j)
        invFun := fun ω j => (ω j).trans (q j).symm
        left_inv := by intro ω; funext j; ext a; simp
        right_inv := by intro ω; funext j; ext a; simp }
    have hτ (ω : Ω) : b (τ ω) = (b ω).image π := by
      simp [b, τ, q, Finset.image_image, Function.comp_def]
    have hevent (ω : Ω) : b (τ ω) = U ↔ b ω = S := by
      rw [hτ, ← hπS]
      exact Finset.image_inj π.injective
    symm
    apply Finset.card_bij (fun ω _ => τ ω)
    · intro ω hω
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hevent ω).mpr (Finset.mem_filter.mp hω).2⟩
    · intro ω _ ω' _ h
      exact τ.injective h
    · intro ω hω
      refine ⟨τ.symm ω, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        τ.apply_symm_apply ω⟩
      exact (hevent (τ.symm ω)).mp (by simpa using (Finset.mem_filter.mp hω).2)
  have htotal : Fintype.card Ω = K.card * c := by
    calc
      _ = ∑ U ∈ K, ((Finset.univ : Finset Ω).filter fun ω => b ω = U).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset Ω)) (t := K) (f := b) (fun ω _ => hb ω))
      _ = K.card * c := Finset.sum_const_nat hfiber
  have hevent : ((Finset.univ : Finset Ω).filter fun ω => P (b ω)).card =
      (K.filter P).card * c := by
    calc
      _ = ∑ U ∈ K.filter P,
          ((Finset.univ : Finset Ω).filter fun ω => b ω = U).card := by
        rw [Finset.sum_card_fiberwise_eq_card_filter]
        congr 1
        ext ω
        simp [hb]
      _ = (K.filter P).card * c :=
        Finset.sum_const_nat (fun U hU => hfiber U (Finset.mem_filter.mp hU).1)
  change _ / (Fintype.card Ω : ℝ) = _
  rw [hevent, htotal, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast hc.ne' : (c : ℝ) ≠ 0)
