import Tablet.VertexSpreadOn

-- [TABLET NODE: VertexSpreadSequential]
theorem VertexSpreadSequential {X Z Y : Type*} (μ : PMF (X → Y))
    (κ : (X → Y) → PMF (Z → Y)) (q : ENNReal)
    (hμ : VertexSpreadOn μ q Set.univ)
    (hκ : ∀ f, VertexSpreadOn (κ f) q Set.univ) :
    VertexSpreadOn
      (μ.bind fun f => (κ f).map (fun g => Sum.elim f g)) q Set.univ := by
-- BODY
  classical
  refine ⟨hμ.1, ?_⟩
  intro s x y hx _
  let L := {i : Fin s // ∃ u : X, x i = Sum.inl u}
  let R := {i : Fin s // ¬∃ u : X, x i = Sum.inl u}
  let left : L → X := fun i => Classical.choose i.property
  have hleft (i : L) : x i.val = Sum.inl (left i) :=
    Classical.choose_spec i.property
  have right_exists (i : R) : ∃ u : Z, x i.val = Sum.inr u := by
    cases hi : x i.val with
    | inl u => exact False.elim (i.property ⟨u, hi⟩)
    | inr u => exact ⟨u, rfl⟩
  let right : R → Z := fun i => Classical.choose (right_exists i)
  have hright (i : R) : x i.val = Sum.inr (right i) :=
    Classical.choose_spec (right_exists i)
  have left_inj : Function.Injective left := by
    intro i j hij
    apply Subtype.ext
    apply hx
    rw [hleft i, hleft j, hij]
  have right_inj : Function.Injective right := by
    intro i j hij
    apply Subtype.ext
    apply hx
    rw [hright i, hright j, hij]
  let a := Fintype.card L
  let b := Fintype.card R
  have hab : a + b = s := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sumCompl (fun i : Fin s => ∃ u : X, x i = Sum.inl u))
  let eL := Fintype.equivFin L
  let eR := Fintype.equivFin R
  let EL : Set (X → Y) := {f | ∀ i : L, f (left i) = y i.val}
  let ER : Set (Z → Y) := {g | ∀ i : R, g (right i) = y i.val}
  have left_cylinder :
      CylinderEvent (fun j : Fin a => left (eL.symm j))
        (fun j => y (eL.symm j).val) = EL := by
    ext f
    change (∀ j, f (left (eL.symm j)) = y (eL.symm j).val) ↔
      ∀ i : L, f (left i) = y i.val
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (eL i)
    · intro h j
      exact h (eL.symm j)
  have right_cylinder :
      CylinderEvent (fun j : Fin b => right (eR.symm j))
        (fun j => y (eR.symm j).val) = ER := by
    ext g
    change (∀ j, g (right (eR.symm j)) = y (eR.symm j).val) ↔
      ∀ i : R, g (right i) = y i.val
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (eR i)
    · intro h j
      exact h (eR.symm j)
  have hEL : μ.toOuterMeasure EL ≤ q ^ a := by
    rw [← left_cylinder]
    exact hμ.2 a _ _ (left_inj.comp eL.symm.injective) (fun _ => Set.mem_univ _)
  have hER (f : X → Y) : (κ f).toOuterMeasure ER ≤ q ^ b := by
    rw [← right_cylinder]
    exact (hκ f).2 b _ _ (right_inj.comp eR.symm.injective)
      (fun _ => Set.mem_univ _)
  have joint_iff (f : X → Y) (g : Z → Y) :
      Sum.elim f g ∈ CylinderEvent x y ↔ f ∈ EL ∧ g ∈ ER := by
    change (∀ i, Sum.elim f g (x i) = y i) ↔
      (∀ i : L, f (left i) = y i.val) ∧ (∀ i : R, g (right i) = y i.val)
    constructor
    · intro h
      constructor
      · intro i
        simpa only [hleft i, Sum.elim_inl] using h i.val
      · intro i
        simpa only [hright i, Sum.elim_inr] using h i.val
    · rintro ⟨hf, hg⟩ i
      by_cases hi : ∃ u : X, x i = Sum.inl u
      · rw [hleft ⟨i, hi⟩]
        exact hf ⟨i, hi⟩
      · rw [hright ⟨i, hi⟩]
        exact hg ⟨i, hi⟩
  have preimage (f : X → Y) :
      (fun g => Sum.elim f g) ⁻¹' CylinderEvent x y =
        if f ∈ EL then ER else ∅ := by
    ext g
    simp only [Set.mem_preimage, joint_iff]
    by_cases hf : f ∈ EL <;> simp [hf]
  have conditional (f : X → Y) :
      ((κ f).map (fun g => Sum.elim f g)).toOuterMeasure (CylinderEvent x y) ≤
        if f ∈ EL then q ^ b else 0 := by
    rw [PMF.toOuterMeasure_map_apply, preimage]
    by_cases hf : f ∈ EL
    · simpa only [hf, if_true] using hER f
    · simp [hf]
  calc
    (μ.bind fun f => (κ f).map (fun g => Sum.elim f g)).toOuterMeasure
        (CylinderEvent x y) =
        ∑' f, μ f * ((κ f).map (fun g => Sum.elim f g)).toOuterMeasure
          (CylinderEvent x y) := PMF.toOuterMeasure_bind_apply _ _ _
    _ ≤ ∑' f, (if f ∈ EL then μ f else 0) * q ^ b := by
      apply ENNReal.tsum_le_tsum
      intro f
      have h := mul_le_mul_right (conditional f) (μ f)
      by_cases hf : f ∈ EL <;> simpa only [hf, if_true, if_false, mul_zero, zero_mul] using h
    _ = μ.toOuterMeasure EL * q ^ b := by
      rw [ENNReal.tsum_mul_right, PMF.toOuterMeasure_apply]
      simp only [Set.indicator_apply]
    _ ≤ q ^ a * q ^ b := mul_le_mul_left hEL _
    _ = q ^ s := by rw [← pow_add, hab]
