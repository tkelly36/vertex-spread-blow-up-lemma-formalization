import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Density

-- [TABLET NODE: ExceptionalCoreEdgeExtension]
theorem ExceptionalCoreEdgeExtension
    {V : Type*} [Fintype V] [DecidableEq V]
    (H F : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel F.Adj]
    (U W U₀ W₀ : Finset V) (k : ℕ)
    (hUW : Disjoint U W) (hU₀ : U₀ ⊆ U) (hW₀ : W₀ ⊆ W)
    (hFH : F ≤ H)
    (hFs : ∀ ⦃u v⦄, F.Adj u v →
      (u ∈ U₀ ∧ v ∈ W₀) ∨ (u ∈ W₀ ∧ v ∈ U₀))
    (hNU : ∀ u ∈ U \ U₀, k ≤ (W₀.filter fun w => H.Adj u w).card)
    (hNW : ∀ w ∈ W \ W₀, k ≤ (U₀.filter fun u => H.Adj w u).card) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      G ≤ H ∧ F ≤ G ∧
      (∀ u ∈ U₀, ∀ w ∈ W₀, G.Adj u w ↔ F.Adj u w) ∧
      (∀ u ∈ U \ U₀, (W.filter fun w => G.Adj u w).card = k) ∧
      (∀ w ∈ W \ W₀, (U.filter fun u => G.Adj w u).card = k) ∧
      (∀ u ∈ U₀,
        (W₀.filter fun w => F.Adj u w).card ≤ (W.filter fun w => G.Adj u w).card ∧
        (W.filter fun w => G.Adj u w).card ≤
          (W₀.filter fun w => F.Adj u w).card + (W \ W₀).card) ∧
      (∀ w ∈ W₀,
        (U₀.filter fun u => F.Adj w u).card ≤ (U.filter fun u => G.Adj w u).card ∧
        (U.filter fun u => G.Adj w u).card ≤
          (U₀.filter fun u => F.Adj w u).card + (U \ U₀).card) := by
-- BODY
  classical
  let BU := U \ U₀
  let BW := W \ W₀
  have hchooseU : ∀ u : V, ∃ S : Finset V,
      S ⊆ W₀ ∧ (∀ w ∈ S, H.Adj u w) ∧ (u ∈ BU → S.card = k) := by
    intro u
    by_cases hu : u ∈ BU
    · obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (hNU u hu)
      exact ⟨S, fun w hw => (Finset.mem_filter.mp (hS hw)).1,
        fun w hw => (Finset.mem_filter.mp (hS hw)).2, fun _ => hcard⟩
    · exact ⟨∅, by simp, by simp, fun h => (hu h).elim⟩
  have hchooseW : ∀ w : V, ∃ S : Finset V,
      S ⊆ U₀ ∧ (∀ u ∈ S, H.Adj w u) ∧ (w ∈ BW → S.card = k) := by
    intro w
    by_cases hw : w ∈ BW
    · obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (hNW w hw)
      exact ⟨S, fun u hu => (Finset.mem_filter.mp (hS hu)).1,
        fun u hu => (Finset.mem_filter.mp (hS hu)).2, fun _ => hcard⟩
    · exact ⟨∅, by simp, by simp, fun h => (hw h).elim⟩
  choose SU hSUsub hSUadj hSUcard using hchooseU
  choose SW hSWsub hSWadj hSWcard using hchooseW
  have hdis : ∀ v ∈ U, v ∉ W := fun v hv hw => Finset.disjoint_left.mp hUW hv hw
  let E : V → V → Prop := fun u v =>
    (u ∈ BU ∧ v ∈ SU u) ∨ (u ∈ BW ∧ v ∈ SW u)
  have hEH : ∀ u v, E u v → H.Adj u v := by
    intro u v h
    rcases h with h | h
    · exact hSUadj u v h.2
    · exact hSWadj u v h.2
  let G : SimpleGraph V :=
    { Adj := fun u v => F.Adj u v ∨ E u v ∨ E v u
      symm := by
        intro u v huv
        rcases huv with huv | huv | huv
        · exact Or.inl huv.symm
        · exact Or.inr (Or.inr huv)
        · exact Or.inr (Or.inl huv)
      loopless := by
        constructor
        intro u huv
        rcases huv with huv | huv | huv
        · exact F.loopless.irrefl u huv
        · exact H.loopless.irrefl u (hEH u u huv)
        · exact H.loopless.irrefl u (hEH u u huv) }
  letI : DecidableRel G.Adj := Classical.decRel _
  have hGH : G ≤ H := by
    intro u v huv
    rcases huv with huv | huv | huv
    · exact hFH huv
    · exact hEH u v huv
    · exact (hEH v u huv).symm
  have hFG : F ≤ G := fun _ _ huv => Or.inl huv
  have hcross : ∀ u ∈ U, ∀ w ∈ W,
      G.Adj u w ↔ F.Adj u w ∨ (u ∈ BU ∧ w ∈ SU u) ∨ (w ∈ BW ∧ u ∈ SW w) := by
    intro u hu w hw
    have huBW : u ∉ BW := fun h => hdis u hu (Finset.mem_sdiff.mp h).1
    have hwBU : w ∉ BU := fun h => hdis w (Finset.mem_sdiff.mp h).1 hw
    change (F.Adj u w ∨ ((u ∈ BU ∧ w ∈ SU u) ∨ (u ∈ BW ∧ w ∈ SW u)) ∨
      ((w ∈ BU ∧ u ∈ SU w) ∨ (w ∈ BW ∧ u ∈ SW w))) ↔ _
    simp only [huBW, hwBU, false_and, or_false, false_or]
  have hagree : ∀ u ∈ U₀, ∀ w ∈ W₀, G.Adj u w ↔ F.Adj u w := by
    intro u hu w hw
    rw [hcross u (hU₀ hu) w (hW₀ hw)]
    have huBU : u ∉ BU := by simp [BU, hu]
    have hwBW : w ∉ BW := by simp [BW, hw]
    simp only [huBU, hwBW, false_and, or_false]
  have hexU : ∀ u ∈ BU, W.filter (fun w => G.Adj u w) = SU u := by
    intro u hu
    have huU := (Finset.mem_sdiff.mp hu).1
    have hu0 := (Finset.mem_sdiff.mp hu).2
    ext w
    constructor
    · intro hw
      obtain ⟨hwW, huw⟩ := Finset.mem_filter.mp hw
      rcases (hcross u huU w hwW).mp huw with hf | hs | hs
      · rcases hFs hf with hf | hf
        · exact (hu0 hf.1).elim
        · exact (hdis u huU (hW₀ hf.1)).elim
      · exact hs.2
      · exact (hu0 (hSWsub w hs.2)).elim
    · intro hw
      exact Finset.mem_filter.mpr ⟨hW₀ (hSUsub u hw),
        (hcross u huU w (hW₀ (hSUsub u hw))).mpr (Or.inr (Or.inl ⟨hu, hw⟩))⟩
  have hexW : ∀ w ∈ BW, U.filter (fun u => G.Adj w u) = SW w := by
    intro w hw
    have hwW := (Finset.mem_sdiff.mp hw).1
    have hw0 := (Finset.mem_sdiff.mp hw).2
    ext u
    constructor
    · intro hu
      obtain ⟨huU, hwu⟩ := Finset.mem_filter.mp hu
      rcases (hcross u huU w hwW).mp hwu.symm with hf | hs | hs
      · rcases hFs hf with hf | hf
        · exact (hw0 hf.2).elim
        · exact (hdis w (hU₀ hf.2) hwW).elim
      · exact (hw0 (hSUsub u hs.2)).elim
      · exact hs.2
    · intro hu
      exact Finset.mem_filter.mpr ⟨hU₀ (hSWsub w hu),
        ((hcross u (hU₀ (hSWsub w hu)) w hwW).mpr
          (Or.inr (Or.inr ⟨hw, hu⟩))).symm⟩
  have hcoreU : ∀ u ∈ U₀,
      (W₀.filter fun w => F.Adj u w).card ≤ (W.filter fun w => G.Adj u w).card ∧
      (W.filter fun w => G.Adj u w).card ≤
        (W₀.filter fun w => F.Adj u w).card + BW.card := by
    intro u hu
    constructor
    · apply Finset.card_le_card
      intro w hw
      obtain ⟨hw0, hf⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hW₀ hw0, hFG hf⟩
    · have hsub : W.filter (fun w => G.Adj u w) ⊆
          (W₀.filter fun w => F.Adj u w) ∪ BW := by
        intro w hw
        obtain ⟨hwW, hg⟩ := Finset.mem_filter.mp hw
        by_cases hw0 : w ∈ W₀
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hw0, (hagree u hu w hw0).mp hg⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwW, hw0⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcoreW : ∀ w ∈ W₀,
      (U₀.filter fun u => F.Adj w u).card ≤ (U.filter fun u => G.Adj w u).card ∧
      (U.filter fun u => G.Adj w u).card ≤
        (U₀.filter fun u => F.Adj w u).card + BU.card := by
    intro w hw
    constructor
    · apply Finset.card_le_card
      intro u hu
      obtain ⟨hu0, hf⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hU₀ hu0, hFG hf⟩
    · have hsub : U.filter (fun u => G.Adj w u) ⊆
          (U₀.filter fun u => F.Adj w u) ∪ BU := by
        intro u hu
        obtain ⟨huU, hg⟩ := Finset.mem_filter.mp hu
        by_cases hu0 : u ∈ U₀
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hu0, ((hagree u hu0 w hw).mp hg.symm).symm⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨huU, hu0⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  exact ⟨G, inferInstance, hGH, hFG, hagree,
    fun u hu => (congrArg Finset.card (hexU u hu)).trans (hSUcard u hu),
    fun w hw => (congrArg Finset.card (hexW w hw)).trans (hSWcard w hw),
    hcoreU, hcoreW⟩
