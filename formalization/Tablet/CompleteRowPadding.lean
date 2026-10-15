import Tablet.LowerSuperRegularPair
import Mathlib.Data.ENNReal.Real

-- [TABLET NODE: CompleteRowPadding]
theorem CompleteRowPadding {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (Gp : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel Gp.Adj]
    (e : V ↪ W) (L Q : Finset V) (D : Finset W)
    (ε η d : ENNReal)
    (hε : 0 < ε) (hbudget : ε ≤ η * η) (hη : η ≤ 1) (hd : d ≤ 1)
    (hdis : Disjoint (L.map e) D)
    (hsize : ((L.map e) ∪ D).card = Q.card)
    (hcopy : ∀ x ∈ L, ∀ y ∈ Q, Gp.Adj (e x) (e y) ↔ G.Adj x y)
    (hcomplete : ∀ z ∈ D, ∀ y ∈ Q, Gp.Adj z (e y))
    (hreg : LowerSuperRegularPair G L Q ε d) :
    LowerSuperRegularPair Gp ((L.map e) ∪ D) (Q.map e) η d := by
-- BODY
  classical
  have heη : ε ≤ η := hbudget.trans (by simpa using mul_le_mul_left' hη η)
  have hηpos : 0 < η := by
    by_contra h
    have : η = 0 := le_antisymm (le_of_not_gt h) (zero_le _)
    simp_all
  by_cases hdη : d ≤ η
  · simp only [LowerSuperRegularPair, LowerRegularPair, tsub_eq_zero_of_le hdη,
      zero_mul, zero_le, implies_true, and_self]
  have hηd : η ≤ d := le_of_lt (lt_of_not_ge hdη)
  have hed : ε ≤ d := heη.trans hηd
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd
  have hηtop : η ≠ ⊤ := ne_top_of_le_ne_top hdtop hηd
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top hdtop hed
  have er : ε.toReal ≤ η.toReal := (ENNReal.toReal_le_toReal hεtop hηtop).2 heη
  have dr : d.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hdtop (by simp)).2 hd
  have ηr : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hηpos) hηtop
  have budgetr : ε.toReal ≤ η.toReal * η.toReal := by
    simpa using (ENNReal.toReal_le_toReal hεtop (ENNReal.mul_ne_top hηtop hηtop)).2 hbudget
  have ηsub : (d - η).toReal = d.toReal - η.toReal := ENNReal.toReal_sub_of_le hηd hdtop
  have εsub : (d - ε).toReal = d.toReal - ε.toReal := ENNReal.toReal_sub_of_le hed hdtop
  have subtop : d - η ≠ ⊤ := ne_top_of_le_ne_top hdtop tsub_le_self
  have esubtop : d - ε ≠ ⊤ := ne_top_of_le_ne_top hdtop tsub_le_self
  let E (S T : Finset V) := ((S.product T).filter fun p => G.Adj p.1 p.2).card
  let Ep (S T : Finset W) := ((S.product T).filter fun p => Gp.Adj p.1 p.2).card
  have cmap (S : Finset V) (hs : S ⊆ L) (T : Finset V) (ht : T ⊆ Q) :
      Ep (S.map e) (T.map e) = E S T := by
    dsimp [E, Ep]
    rw [← Finset.prodMap_map_product, Finset.filter_map]
    have heq : (S.product T).filter (fun p => Gp.Adj (e p.1) (e p.2)) =
        (S.product T).filter (fun p => G.Adj p.1 p.2) := by
      apply Finset.filter_congr
      intro p hp
      exact hcopy p.1 (hs (Finset.mem_product.mp hp).1)
        p.2 (ht (Finset.mem_product.mp hp).2)
    simpa [Function.Embedding.prodMap] using congrArg Finset.card heq
  have cadd (S : Finset V) (hs : S ⊆ L) (D' : Finset W) (hD : D' ⊆ D)
      (T : Finset V) (ht : T ⊆ Q) :
      Ep ((S.map e) ∪ D') (T.map e) = E S T + D'.card * T.card := by
    have hsd : Disjoint (S.map e) D' := hdis.mono (Finset.map_subset_map.mpr hs) hD
    dsimp [E, Ep]
    rw [Finset.union_product, Finset.filter_union,
      Finset.card_union_of_disjoint
        ((Finset.disjoint_product.mpr (Or.inl hsd)).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    change Ep (S.map e) (T.map e) + Ep D' (T.map e) = E S T + D'.card * T.card
    have hfcard : Ep D' (T.map e) = D'.card * T.card := by
      dsimp [Ep]
      calc
        _ = (D'.product (T.map e)).card := by
          apply congrArg Finset.card
          apply Finset.filter_eq_self.mpr
          rintro ⟨z, w⟩ hp
          obtain ⟨hz, hw⟩ := Finset.mem_product.mp hp
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
          exact hcomplete z (hD hz) y (ht hy)
        _ = _ := by simp
    rw [hfcard]
    exact congrArg (fun n => n + D'.card * T.card) (cmap S hs T ht)
  have sizes : L.card + D.card = Q.card := by
    simpa [Finset.card_union_of_disjoint hdis] using hsize
  have ml : L.card ≤ Q.card := by omega
  have oldbound (S T : Finset V) (hs : S ⊆ L) (ht : T ⊆ Q)
      (hS : ε * (L.card : ENNReal) < S.card)
      (hT : ε * (Q.card : ENNReal) < T.card) :
      (d.toReal - ε.toReal) * (S.card : ℝ) * (T.card : ℝ) ≤ E S T := by
    have hp := hreg.1 S hs T ht hS hT
    have sn : S.card ≠ 0 := by intro h; simp [h] at hS
    have tn : T.card ≠ 0 := by intro h; simp [h] at hT
    have pos : 0 < (S.card : ℝ) * (T.card : ℝ) := by positivity
    have den : (S.card : ENNReal) * T.card ≠ 0 := by simp [sn, tn]
    have pt : PairDensity G S T ≠ ⊤ := by
      dsimp [PairDensity]
      exact ENNReal.div_ne_top (by simp) den
    have hp' := (ENNReal.toReal_le_toReal esubtop pt).2 hp
    simp only [εsub, PairDensity, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast] at hp'
    simpa [E, mul_assoc] using (le_div_iff₀ pos).mp hp'
  refine ⟨?_, ?_, ?_⟩
  · intro S hS T hT hSt hTt
    let S₀ := L.filter fun x => e x ∈ S
    let T₀ := Q.filter fun y => e y ∈ T
    let SD := S ∩ D
    have hs₀ : S₀ ⊆ L := Finset.filter_subset _ _
    have ht₀ : T₀ ⊆ Q := Finset.filter_subset _ _
    have hd₀ : SD ⊆ D := Finset.inter_subset_right
    have teq : T = T₀.map e := by
      ext w
      constructor
      · intro hw
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp (hT hw)
        exact Finset.mem_map.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hw⟩, rfl⟩
      · intro hw
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
        exact (Finset.mem_filter.mp hy).2
    have seq : S = (S₀.map e) ∪ SD := by
      ext w
      constructor
      · intro hw
        rcases Finset.mem_union.mp (hS hw) with ho | hd'
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ho
          exact Finset.mem_union_left _ (Finset.mem_map.mpr
            ⟨x, Finset.mem_filter.mpr ⟨hx, hw⟩, rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw, hd'⟩)
      · intro hw
        rcases Finset.mem_union.mp hw with ho | hd'
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ho
          exact (Finset.mem_filter.mp hx).2
        · exact (Finset.mem_inter.mp hd').1
    have sc : S.card = S₀.card + SD.card := by
      rw [seq, Finset.card_union_of_disjoint (hdis.mono (Finset.map_subset_map.mpr hs₀) hd₀),
        Finset.card_map]
    have tc : T.card = T₀.card := by rw [teq, Finset.card_map]
    have ec : Ep S T = E S₀ T₀ + SD.card * T₀.card := by
      rw [seq, teq]; exact cadd S₀ hs₀ SD hd₀ T₀ ht₀
    have tr : η.toReal * (Q.card : ℝ) < T₀.card := by
      rw [Finset.card_map, tc] at hTt
      simpa using (ENNReal.toReal_lt_toReal
        (ENNReal.mul_ne_top hηtop (by simp)) (by simp)).2 hTt
    have sr : η.toReal * (Q.card : ℝ) < S.card := by
      rw [hsize] at hSt
      simpa using (ENNReal.toReal_lt_toReal
        (ENNReal.mul_ne_top hηtop (by simp)) (by simp)).2 hSt
    have spos : 0 < (S.card : ℝ) := lt_of_le_of_lt
      (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) sr
    have tpos : 0 < (T.card : ℝ) := by
      rw [tc]
      exact lt_of_le_of_lt (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) tr
    have edge : (d.toReal - η.toReal) * (S.card : ℝ) * (T.card : ℝ) ≤ Ep S T := by
      rw [ec, Nat.cast_add, Nat.cast_mul, tc]
      have scr : (S.card : ℝ) = (S₀.card : ℝ) + SD.card := by exact_mod_cast sc
      by_cases ho : ε * (L.card : ENNReal) < S₀.card
      · have ot : ε * (Q.card : ENNReal) < T₀.card :=
          lt_of_le_of_lt (mul_le_mul_right' heη _) (by
            rw [Finset.card_map, tc] at hTt
            exact hTt)
        have old := oldbound S₀ T₀ hs₀ ht₀ ho ot
        have c₁ := mul_nonneg (sub_nonneg.mpr er) (Nat.cast_nonneg S₀.card : (0 : ℝ) ≤ _)
        have c₂ := mul_nonneg (sub_nonneg.mpr (show d.toReal - η.toReal ≤ 1 by linarith))
          (Nat.cast_nonneg SD.card : (0 : ℝ) ≤ _)
        rw [scr]
        nlinarith [mul_nonneg c₁ (Nat.cast_nonneg T₀.card : (0 : ℝ) ≤ _),
          mul_nonneg c₂ (Nat.cast_nonneg T₀.card : (0 : ℝ) ≤ _)]
      · have oa : (S₀.card : ENNReal) ≤ ε * L.card := le_of_not_gt ho
        have oar : (S₀.card : ℝ) ≤ ε.toReal * L.card := by
          simpa using (ENNReal.toReal_le_toReal (by simp)
            (ENNReal.mul_ne_top hεtop (by simp))).2 oa
        have mlr : (L.card : ℝ) ≤ Q.card := by exact_mod_cast ml
        have an : (S₀.card : ℝ) ≤ ε.toReal * Q.card := by
          nlinarith [mul_nonneg (ENNReal.toReal_nonneg (a := ε)) (sub_nonneg.mpr mlr)]
        have aq : (S₀.card : ℝ) ≤ η.toReal * η.toReal * Q.card := by
          nlinarith [mul_nonneg (sub_nonneg.mpr budgetr) (Nat.cast_nonneg Q.card : (0 : ℝ) ≤ _)]
        have asmall : (S₀.card : ℝ) ≤ η.toReal * S.card := by nlinarith
        have lower : (d.toReal - η.toReal) * S.card ≤ SD.card := by
          nlinarith [mul_nonneg (sub_nonneg.mpr dr) (Nat.cast_nonneg S.card : (0 : ℝ) ≤ _)]
        nlinarith [mul_nonneg (sub_nonneg.mpr lower)
          (Nat.cast_nonneg T₀.card : (0 : ℝ) ≤ _), (Nat.cast_nonneg (E S₀ T₀) : (0 : ℝ) ≤ _)]
    have sn : S.card ≠ 0 := by exact_mod_cast (ne_of_gt spos)
    have tn : T.card ≠ 0 := by exact_mod_cast (ne_of_gt tpos)
    apply (ENNReal.toReal_le_toReal subtop
      (ENNReal.div_ne_top (by simp) (by simp [sn, tn]))).1
    simp only [ηsub, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact (le_div_iff₀ (mul_pos spos tpos)).2 (by simpa [Ep, mul_assoc] using edge)
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      have roweq : ((Q.map e).filter fun w => Gp.Adj (e x) w).card =
          (Q.filter fun y => G.Adj x y).card := by
        rw [Finset.filter_map, Finset.card_map]
        congr 1
        apply Finset.filter_congr
        intro y hy
        exact hcopy x hx y hy
      rw [Finset.card_map, roweq]
      exact (mul_le_mul_right' (tsub_le_tsub_left heη d) _).trans (hreg.2.1 x hx)
    · have roweq : (Q.map e).filter (fun w => Gp.Adj z w) = Q.map e := by
        apply Finset.filter_eq_self.mpr
        intro w hw
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
        exact hcomplete z hz y hy
      rw [roweq, Finset.card_map]
      simpa using mul_le_mul_right' (tsub_le_self.trans hd) (Q.card : ENNReal)
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hw
    have col : (((L.map e) ∪ D).filter fun z => Gp.Adj z (e y)).card =
        (L.filter fun x => G.Adj x y).card + D.card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint
        (hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      have drow : D.filter (fun z => Gp.Adj z (e y)) = D :=
        Finset.filter_eq_self.mpr (fun z hz => hcomplete z hz y hy)
      rw [drow, Finset.filter_map, Finset.card_map]
      congr 2
      apply Finset.filter_congr
      intro x hx
      exact hcopy x hx y hy
    rw [hsize, col]
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top subtop (by simp)) (by simp)).1
    have old := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top esubtop (by simp)) (by simp)).2 (hreg.2.2 y hy)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, εsub] at old
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ηsub]
    push_cast
    have sz : (Q.card : ℝ) = (L.card : ℝ) + D.card := by exact_mod_cast sizes.symm
    nlinarith [mul_nonneg (sub_nonneg.mpr er) (show 0 ≤ (L.card : ℝ) by positivity),
      mul_nonneg (sub_nonneg.mpr (show d.toReal - η.toReal ≤ 1 by linarith))
        (show 0 ≤ (D.card : ℝ) by positivity)]
