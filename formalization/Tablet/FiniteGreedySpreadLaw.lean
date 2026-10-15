import Tablet.VertexSpreadSequential
import Tablet.VertexSpreadRestriction

-- [TABLET NODE: FiniteGreedySpreadLaw]
theorem FiniteGreedySpreadLaw {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V]
    (q : ENNReal) (hq : q ≤ 1)
    (T : U → Finset V) (hT : ∀ u, (T u).Nonempty)
    (hTq : ∀ u, 1 / ((T u).card : ENNReal) ≤ q)
    (Good : Finset U → (U → V) → Prop)
    (hlocal : ∀ S f g, (∀ u ∈ S, f u = g u) → (Good S f ↔ Good S g))
    (hzero : ∀ f, Good ∅ f)
    (hstep : ∀ S f z, z ∉ S → Good S f →
      ∃ L : Finset V, L.Nonempty ∧ 1 / (L.card : ENNReal) ≤ q ∧
        ∀ v ∈ L, Good (insert z S) (Function.update f z v)) :
    ∀ S : Finset U, ∃ μ : PMF {f : U → V // Good S f},
      VertexSpreadOn (μ.map Subtype.val) q Set.univ := by
-- BODY
  classical
  let b : U → V := fun u => (hT u).choose
  let extend (A : Finset U) (f : A → V) : U → V :=
    fun u => if hu : u ∈ A then f ⟨u, hu⟩ else b u
  have extend_on (A : Finset U) (f : A → V) (u : A) :
      extend A f u = f u := by simp [extend, u.property]
  have reference_independent (A : Finset U) (f : A → V) (g : U → V)
      (hg : ∀ u : A, g u = f u) : Good A (extend A f) ↔ Good A g := by
    apply hlocal A (extend A f) g
    intro u hu
    exact (extend_on A f ⟨u, hu⟩).trans (hg ⟨u, hu⟩).symm
  have uniform_spread (L : Finset V) (hL : L.Nonempty)
      (hLq : 1 / (L.card : ENNReal) ≤ q) :
      VertexSpreadOn ((PMF.uniformOfFinset L hL).map
        (fun v => fun _ : Unit => v)) q Set.univ := by
    refine ⟨hq, ?_⟩
    intro s x y hx _
    have hs : s ≤ 1 := by
      simpa using Fintype.card_le_of_injective x hx
    cases s with
    | zero =>
      have hevent : CylinderEvent x y = Set.univ := by ext f; simp [CylinderEvent]
      rw [hevent, pow_zero]
      exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
    | succ s =>
      have hs0 : s = 0 := by omega
      subst s
      rw [PMF.toOuterMeasure_map_apply]
      have hevent : (fun v => fun _ : Unit => v) ⁻¹' CylinderEvent x y = {y 0} := by
        ext v
        simp [CylinderEvent, Fin.forall_fin_one]
      rw [hevent]
      calc
        _ = ((L.filter fun v => v ∈ ({y 0} : Set V)).card : ENNReal) /
            (L.card : ENNReal) := by
          convert PMF.toOuterMeasure_uniformOfFinset_apply hL {y 0} using 1
          congr 2
          apply congrArg Finset.card
          ext v
          simp
        _ ≤ q ^ (0 + 1) := by
          have hcard : (L.filter (fun v => v ∈ ({y 0} : Set V))).card ≤ 1 := by
            calc
              _ ≤ ({y 0} : Finset V).card := Finset.card_le_card (by
                intro v hv
                simpa using (Finset.mem_filter.mp hv).2)
              _ = 1 := Finset.card_singleton _
          have hcard' : ((L.filter (fun v => v ∈ ({y 0} : Set V))).card : ENNReal) ≤ 1 :=
            by exact_mod_cast hcard
          simpa only [Nat.zero_add, pow_one] using
            (ENNReal.div_le_div_right hcard' (L.card : ENNReal)).trans hLq
  have prefixes : ∀ (G : Finset U → (U → V) → Prop),
      (∀ A f g, (∀ u ∈ A, f u = g u) → (G A f ↔ G A g)) →
      (∀ f, G ∅ f) →
      ∀ (K : ∀ A : Finset U, (A → V) → U → Finset V),
      (∀ A f z, z ∉ A →
        (K A f z).Nonempty ∧ 1 / ((K A f z).card : ENNReal) ≤ q ∧
          (G A (extend A f) → ∀ v ∈ K A f z,
            G (insert z A) (Function.update (extend A f) z v))) →
      ∀ A : Finset U, ∃ ν : PMF (A → V),
        VertexSpreadOn ν q Set.univ ∧
        ∀ f ∈ ν.support, G A (extend A f) := by
    intro G hGloc hGzero K hK A
    induction A using Finset.induction_on with
    | empty =>
      let f0 : (∅ : Finset U) → V := fun u => False.elim (Finset.notMem_empty _ u.property)
      refine ⟨PMF.pure f0, ⟨hq, ?_⟩, ?_⟩
      · intro s x y hx hy
        cases s with
        | zero =>
          have hevent : CylinderEvent x y = Set.univ := by ext f; simp [CylinderEvent]
          rw [hevent, pow_zero]
          exact le_of_eq ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
        | succ s => exact False.elim (Finset.notMem_empty _ (x 0).property)
      · intro f hf
        exact hGzero _
    | @insert z A hz ih =>
      obtain ⟨ν, hν, hvalid⟩ := ih
      let L (f : A → V) := K A f z
      have hL (f : A → V) : (L f).Nonempty := (hK A f z hz).1
      have hLq (f : A → V) : 1 / ((L f).card : ENNReal) ≤ q := (hK A f z hz).2.1
      have hLG (f : A → V) := (hK A f z hz).2.2
      let κ (f : A → V) : PMF (Unit → V) :=
        (PMF.uniformOfFinset (L f) (hL f)).map (fun v => fun _ => v)
      have hκ (f : A → V) : VertexSpreadOn (κ f) q Set.univ :=
        uniform_spread (L f) (hL f) (hLq f)
      let e : (insert z A : Finset U) ≃ (A ⊕ Unit) :=
        { toFun := fun u => if hu : u.val = z then Sum.inr () else
            Sum.inl ⟨u.val, (Finset.mem_insert.mp u.property).resolve_left hu⟩
          invFun := Sum.elim (fun u => ⟨u.val, Finset.mem_insert_of_mem u.property⟩)
            (fun _ => ⟨z, Finset.mem_insert_self z A⟩)
          left_inv := by
            intro u
            dsimp
            split
            · rename_i hu
              exact Subtype.ext hu.symm
            · rfl
          right_inv := by
            intro u
            cases u with
            | inl u =>
              have hu : u.val ≠ z := by intro he; exact hz (he ▸ u.property)
              simp [hu]
            | inr u => cases u; simp }
      let joint : PMF ((A ⊕ Unit) → V) :=
        ν.bind fun f => (κ f).map (Sum.elim f)
      let out : PMF (↥(insert z A) → V) :=
        joint.map (fun k => k ∘ e.toFun)
      refine ⟨out, ?_, ?_⟩
      · exact VertexSpreadRestriction e.toEmbedding (VertexSpreadSequential ν κ q hν hκ)
      · intro f hf
        obtain ⟨k, hk, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hf
        obtain ⟨g, hg, hkg⟩ := (PMF.mem_support_bind_iff _ _ _).mp hk
        obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkg
        obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
        have hvL : v ∈ L g := (PMF.mem_support_uniformOfFinset_iff _ _).mp hv
        have hgood := hLG g (hvalid g hg) v hvL
        apply (hGloc (insert z A) _ _ ?_).mp hgood
        intro u hu
        by_cases huz : u = z
        · subst u
          simp [extend, e]
        · have huA : u ∈ A := (Finset.mem_insert.mp hu).resolve_left huz
          simp [extend, e, hu, huA, huz]
  intro S
  let K (A : Finset U) (f : A → V) (z : U) : Finset V :=
    if hz : z ∉ A then
      if hf : Good A (extend A f) then (hstep A (extend A f) z hz hf).choose
      else T z
    else T z
  have hK : ∀ A f z, z ∉ A →
      (K A f z).Nonempty ∧ 1 / ((K A f z).card : ENNReal) ≤ q ∧
        (Good A (extend A f) → ∀ v ∈ K A f z,
          Good (insert z A) (Function.update (extend A f) z v)) := by
    intro A f z hz
    by_cases hf : Good A (extend A f)
    · simpa only [K, dif_pos hz, dif_pos hf] using
        ⟨(hstep A (extend A f) z hz hf).choose_spec.1,
          (hstep A (extend A f) z hz hf).choose_spec.2.1,
          fun _ => (hstep A (extend A f) z hz hf).choose_spec.2.2⟩
    · simp only [K, dif_pos hz, dif_neg hf]
      exact ⟨hT z, hTq z, fun h => False.elim (hf h)⟩
  obtain ⟨ν, hν, hvalid⟩ := prefixes Good hlocal hzero K hK S
  -- The complement law has constant kernels, independently uniform in T(z).
  let C : Finset U := Finset.univ \ S
  obtain ⟨ρ, hρ, _⟩ := prefixes (fun _ _ => True)
    (fun _ _ _ _ => Iff.rfl) (fun _ => trivial)
    (fun _ _ z => T z) (fun _ _ z _ => ⟨hT z, hTq z, fun _ _ _ => trivial⟩) C
  let eU : U ≃ (S ⊕ C) :=
    { toFun := fun u => if hu : u ∈ S then Sum.inl ⟨u, hu⟩
        else Sum.inr ⟨u, by simp [C, hu]⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro u; dsimp; split <;> rfl
      right_inv := by
        intro u
        cases u with
        | inl u => simp [u.property]
        | inr u =>
          have hu : u.val ∉ S := (Finset.mem_sdiff.mp u.property).2
          simp [hu] }
  let joint : PMF ((S ⊕ C) → V) := ν.bind fun f => ρ.map (Sum.elim f)
  let total : PMF (U → V) := joint.map (fun f => f ∘ eU)
  have htotal : VertexSpreadOn total q Set.univ :=
    VertexSpreadRestriction eU.toEmbedding (VertexSpreadSequential ν (fun _ => ρ) q hν (fun _ => hρ))
  have total_valid : ∀ f ∈ total.support, Good S f := by
    intro f hf
    obtain ⟨k, hk, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hf
    obtain ⟨g, hg, hkg⟩ := (PMF.mem_support_bind_iff _ _ _).mp hk
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hkg
    apply (reference_independent S g _ ?_).mp (hvalid g hg)
    intro u
    simp [eU, u.property]
  obtain ⟨f0, hf0⟩ := total.support_nonempty
  let pack : (U → V) → {f : U → V // Good S f} := fun f =>
    if hf : f ∈ total.support then ⟨f, total_valid f hf⟩
    else ⟨f0, total_valid f0 hf0⟩
  have projected : (total.map pack).map Subtype.val = total := by
    rw [PMF.map_comp]
    have heq : total.map (Subtype.val ∘ pack) = total.map id := by
      apply PMF.ext
      intro f
      simp only [PMF.map_apply]
      apply tsum_congr
      intro g
      by_cases hg : g ∈ total.support
      · simp only [Function.comp_apply, pack, dif_pos hg, id_eq]
        split_ifs <;> rfl
      · have hg0 : total g = 0 := by simpa only [PMF.mem_support_iff, not_not] using hg
        simp [hg0]
    exact heq.trans (PMF.map_id total)
  refine ⟨total.map pack, ?_⟩
  rw [projected]
  exact htotal
