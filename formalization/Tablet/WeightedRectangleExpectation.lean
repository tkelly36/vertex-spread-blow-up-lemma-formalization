import Tablet.Preamble
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

-- [TABLET NODE: WeightedRectangleExpectation]
theorem WeightedRectangleExpectation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (n l : ℕ) (d γ α : ℝ) (hU : U.card = n) (hW : W.card = n)
    (hd : 0 < d) (hd1 : d ≤ 1) (hγ : 0 < γ) (hα : 0 < α)
    (P : Finpartition (Finset.univ : Finset V))
    (E : Finset (Finset V × Finset V)) (hEP : E ⊆ P.parts.product P.parts)
    (hD : ∀ S T, (S, T) ∈ E →
      d ≤ (G.edgeDensity (U ∩ S) (W ∩ T) : ℝ) ∧
      (G.edgeDensity (U ∩ S) (W ∩ T) : ℝ) ≤ 1)
    (hslice : ∀ S T, (S, T) ∈ E → ∀ A ⊆ U ∩ S, ∀ B ⊆ W ∩ T,
      γ * (U ∩ S).card < (A.card : ℝ) →
      γ * (W ∩ T).card < (B.card : ℝ) →
      |(G.edgeDensity A B : ℝ) - G.edgeDensity (U ∩ S) (W ∩ T)| < 2 * α)
    (harea : (∑ ST ∈ (P.parts.product P.parts).filter (fun ST => ST ∉ E),
      (((U ∩ ST.1).card : ℝ) * (W ∩ ST.2).card)) ≤
      (4 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2) :
    ∃ p : V × V → ℝ,
      (∀ e, 0 ≤ p e ∧ p e ≤ 1) ∧
      (∀ e, ¬G.Adj e.1 e.2 → p e = 0) ∧
      (∀ e, e ∉ U.product W → p e = 0) ∧
      (∀ S ∈ P.parts, ∀ T ∈ P.parts,
        ∀ u ∈ U ∩ S, ∀ w ∈ W ∩ T, G.Adj u w →
        p (u, w) = if (S, T) ∈ E then
          d / (G.edgeDensity (U ∩ S) (W ∩ T) : ℝ) else 1) ∧
      (∀ A ⊆ U, ∀ B ⊆ W,
        |(∑ e ∈ A.product B, p e) - d * A.card * B.card| ≤
          2 * α * A.card * B.card +
            (6 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2) ∧
      (∀ h : ℝ, 0 < h →
        2 * α + (6 * γ + 9 * α + 6 / (l : ℝ)) / h ^ 2 < h / 4 →
        ∀ A ⊆ U, ∀ B ⊆ W, h * n < (A.card : ℝ) →
        h * n < (B.card : ℝ) →
        |(∑ e ∈ A.product B, p e) - d * A.card * B.card| <
          (h / 4) * A.card * B.card) := by
-- BODY
  classical
  let q : Finset V × Finset V → ℝ := fun ST =>
    if ST ∈ E then d / (G.edgeDensity (U ∩ ST.1) (W ∩ ST.2) : ℝ) else 1
  let p : V × V → ℝ := fun e =>
    if e ∈ U.product W ∧ G.Adj e.1 e.2 then q (P.part e.1, P.part e.2) else 0
  have hq : ∀ ST ∈ P.parts.product P.parts, 0 ≤ q ST ∧ q ST ≤ 1 := by
    intro ST hST
    dsimp [q]
    split_ifs with he
    · have hD' := hD ST.1 ST.2 he
      have hpos : 0 < (G.edgeDensity (U ∩ ST.1) (W ∩ ST.2) : ℝ) :=
        lt_of_lt_of_le hd hD'.1
      exact ⟨div_nonneg hd.le hpos.le, (div_le_one hpos).2 hD'.1⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    dsimp [p]
    split_ifs
    · exact hq _ (Finset.mem_product.mpr
        ⟨P.part_mem.mpr (Finset.mem_univ _), P.part_mem.mpr (Finset.mem_univ _)⟩)
    · exact ⟨le_rfl, zero_le_one⟩
  have hpne : ∀ e, ¬G.Adj e.1 e.2 → p e = 0 := by
    intro e he
    simp [p, he]
  have hpout : ∀ e, e ∉ U.product W → p e = 0 := by
    intro e he
    exact if_neg (fun h => he h.1)
  have hpformula : ∀ S ∈ P.parts, ∀ T ∈ P.parts,
      ∀ u ∈ U ∩ S, ∀ w ∈ W ∩ T, G.Adj u w → p (u, w) = q (S, T) := by
    intro S hS T hT u hu w hw hadj
    have hpartu := P.part_eq_of_mem hS (Finset.mem_inter.mp hu).2
    have hpartw := P.part_eq_of_mem hT (Finset.mem_inter.mp hw).2
    have hcross : (u, w) ∈ U.product W := Finset.mem_product.mpr
      ⟨(Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hw).1⟩
    dsimp only [p]
    rw [if_pos (And.intro hcross hadj), hpartu, hpartw]
  have hchunks : ∀ (X : Finset V) (f : V → ℝ),
      (∑ S ∈ P.parts, ∑ x ∈ X ∩ S, f x) = ∑ x ∈ X, f x := by
    intro X f
    have hfiber : ∀ S ∈ P.parts, X.filter (fun x => P.part x = S) = X ∩ S := by
      intro S hS
      ext x
      simp only [Finset.mem_filter, Finset.mem_inter, P.part_eq_iff_mem hS]
    have := Finset.sum_fiberwise_of_maps_to
      (s := X) (t := P.parts) (g := P.part)
      (fun x _ => P.part_mem.mpr (Finset.mem_univ x)) f
    calc
      _ = ∑ S ∈ P.parts, ∑ x ∈ X.filter (fun x => P.part x = S), f x := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [hfiber S hS]
      _ = _ := this
  have hcards : ∀ X : Finset V, (∑ S ∈ P.parts, ((X ∩ S).card : ℝ)) = X.card := by
    intro X
    simpa using hchunks X (fun _ => 1)
  have hrects : ∀ (X Y : Finset V) (f : V × V → ℝ),
      (∑ ST ∈ P.parts.product P.parts, ∑ e ∈ (X ∩ ST.1).product (Y ∩ ST.2), f e) =
        ∑ e ∈ X.product Y, f e := by
    intro X Y f
    have hfiber : ∀ ST ∈ P.parts.product P.parts,
        (X.product Y).filter (fun e => (P.part e.1, P.part e.2) = ST) =
          (X ∩ ST.1).product (Y ∩ ST.2) := by
      rintro ⟨S, T⟩ hST
      obtain ⟨hS, hT⟩ := Finset.mem_product.mp hST
      ext e
      simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_inter,
        Prod.mk.injEq, P.part_eq_iff_mem hS, P.part_eq_iff_mem hT]
      tauto
    have := Finset.sum_fiberwise_of_maps_to
      (s := X.product Y) (t := P.parts.product P.parts)
      (g := fun e => (P.part e.1, P.part e.2))
      (fun e _ => Finset.mem_product.mpr
        ⟨P.part_mem.mpr (Finset.mem_univ _), P.part_mem.mpr (Finset.mem_univ _)⟩) f
    calc
      _ = ∑ ST ∈ P.parts.product P.parts,
          ∑ e ∈ (X.product Y).filter (fun e => (P.part e.1, P.part e.2) = ST), f e := by
        apply Finset.sum_congr rfl
        intro ST hST
        rw [hfiber ST hST]
      _ = _ := this
  have hareas : ∀ X Y : Finset V,
      (∑ ST ∈ P.parts.product P.parts,
        ((X ∩ ST.1).card : ℝ) * (Y ∩ ST.2).card) = (X.card : ℝ) * Y.card := by
    intro X Y
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    simp only [← Finset.mul_sum, hcards, ← Finset.sum_mul]
  have hcount : ∀ A B : Finset V, A.Nonempty → B.Nonempty →
      ((G.interedges A B).card : ℝ) = (G.edgeDensity A B : ℝ) * A.card * B.card := by
    intro A B hA hB
    have hAc : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    have hBc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
    simp only [SimpleGraph.edgeDensity_def, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    field_simp [hAc, hBc]
  have hcoarse : ∀ A ⊆ U, ∀ B ⊆ W,
      |(∑ e ∈ A.product B, p e) - d * A.card * B.card| ≤
        2 * α * A.card * B.card + (6 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2 := by
    intro A hA B hB
    let a : Finset V → ℝ := fun S => (A ∩ S).card
    let b : Finset V → ℝ := fun T => (B ∩ T).card
    let u : Finset V → ℝ := fun S => (U ∩ S).card
    let w : Finset V → ℝ := fun T => (W ∩ T).card
    let z : Finset V × Finset V → ℝ := fun ST =>
      ∑ e ∈ (A ∩ ST.1).product (B ∩ ST.2), p e
    have hAs : ∀ S, A ∩ S ⊆ U ∩ S := by
      intro S x hx
      exact Finset.mem_inter.mpr ⟨hA (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
    have hBs : ∀ T, B ∩ T ⊆ W ∩ T := by
      intro T x hx
      exact Finset.mem_inter.mpr ⟨hB (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
    have ha0 : ∀ S, 0 ≤ a S := fun S => Nat.cast_nonneg _
    have hb0 : ∀ T, 0 ≤ b T := fun T => Nat.cast_nonneg _
    have hu0 : ∀ S, 0 ≤ u S := fun S => Nat.cast_nonneg _
    have hw0 : ∀ T, 0 ≤ w T := fun T => Nat.cast_nonneg _
    have hau : ∀ S, a S ≤ u S := fun S => by
      dsimp only [a, u]
      exact_mod_cast Finset.card_le_card (hAs S)
    have hbw : ∀ T, b T ≤ w T := fun T => by
      dsimp only [b, w]
      exact_mod_cast Finset.card_le_card (hBs T)
    have hz0 : ∀ ST, 0 ≤ z ST := by
      intro ST
      exact Finset.sum_nonneg (fun e _ => (hp e).1)
    have hz1 : ∀ ST, z ST ≤ a ST.1 * b ST.2 := by
      intro ST
      calc
        z ST ≤ ∑ _e ∈ (A ∩ ST.1).product (B ∩ ST.2), (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => (hp e).2)
        _ = a ST.1 * b ST.2 := by simp [a, b, Finset.card_product]
    have hrough : ∀ ST, |z ST - d * a ST.1 * b ST.2| ≤ a ST.1 * b ST.2 := by
      intro ST
      have htarget0 : 0 ≤ d * a ST.1 * b ST.2 := by positivity
      have htarget1 : d * a ST.1 * b ST.2 ≤ a ST.1 * b ST.2 := by
        nlinarith only [hd1, mul_nonneg (ha0 ST.1) (hb0 ST.2)]
      exact abs_sub_le_iff.mpr ⟨by linarith only [hz1 ST, htarget0],
        by linarith only [hz0 ST, htarget1]⟩
    have hzcount : ∀ ST ∈ P.parts.product P.parts,
        z ST = q ST * ((G.interedges (A ∩ ST.1) (B ∩ ST.2)).card : ℝ) := by
      intro ST hST
      obtain ⟨hS, hT⟩ := Finset.mem_product.mp hST
      calc
        z ST = ∑ e ∈ (A ∩ ST.1).product (B ∩ ST.2),
            if G.Adj e.1 e.2 then q ST else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          obtain ⟨heA, heB⟩ := Finset.mem_product.mp he
          by_cases hadj : G.Adj e.1 e.2
          · rw [if_pos hadj]
            exact hpformula ST.1 hS ST.2 hT e.1 (hAs _ heA) e.2 (hBs _ heB) hadj
          · rw [if_neg hadj, hpne e hadj]
        _ = ∑ _e ∈ G.interedges (A ∩ ST.1) (B ∩ ST.2), q ST := by
          rw [SimpleGraph.interedges_def, Finset.sum_filter]
          simp only [Finset.product_eq_sprod]
        _ = _ := by simp [mul_comm]
    have hgood : ∀ ST ∈ P.parts.product P.parts, ST ∈ E →
        γ * u ST.1 < a ST.1 → γ * w ST.2 < b ST.2 →
        |z ST - d * a ST.1 * b ST.2| ≤ 2 * α * a ST.1 * b ST.2 := by
      intro ST hST he hlargeA hlargeB
      have hapos : 0 < a ST.1 := lt_of_le_of_lt (mul_nonneg hγ.le (hu0 _)) hlargeA
      have hbpos : 0 < b ST.2 := lt_of_le_of_lt (mul_nonneg hγ.le (hw0 _)) hlargeB
      have hAn : (A ∩ ST.1).Nonempty := Finset.card_pos.mp (by
        dsimp only [a] at hapos
        exact_mod_cast hapos)
      have hBn : (B ∩ ST.2).Nonempty := Finset.card_pos.mp (by
        dsimp only [b] at hbpos
        exact_mod_cast hbpos)
      have hden : 0 < (G.edgeDensity (U ∩ ST.1) (W ∩ ST.2) : ℝ) :=
        lt_of_lt_of_le hd (hD _ _ he).1
      have hslice' := (hslice _ _ he _ (hAs _) _ (hBs _) hlargeA hlargeB).le
      have hqST : q ST = d / (G.edgeDensity (U ∩ ST.1) (W ∩ ST.2) : ℝ) := by
        simp only [q, if_pos he]
      have hfactor : z ST - d * a ST.1 * b ST.2 =
          q ST * ((G.edgeDensity (A ∩ ST.1) (B ∩ ST.2) : ℝ) -
            G.edgeDensity (U ∩ ST.1) (W ∩ ST.2)) * (a ST.1 * b ST.2) := by
        rw [hzcount ST hST, hcount _ _ hAn hBn, hqST]
        dsimp only [a, b]
        field_simp [hden.ne']
      rw [hfactor, abs_mul, abs_mul, abs_of_nonneg (hq ST hST).1,
        abs_of_nonneg (mul_nonneg (ha0 _) (hb0 _))]
      calc
        _ ≤ 1 * (2 * α) * (a ST.1 * b ST.2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (hq ST hST).2 hslice' (abs_nonneg _) zero_le_one)
            (mul_nonneg (ha0 _) (hb0 _))
        _ = _ := by ring
    have hpoint : ∀ ST ∈ P.parts.product P.parts,
        |z ST - d * a ST.1 * b ST.2| ≤
          2 * α * a ST.1 * b ST.2 +
          (if ST ∉ E then u ST.1 * w ST.2 else 0) +
          γ * u ST.1 * b ST.2 + γ * a ST.1 * w ST.2 := by
      intro ST hST
      have hgood0 : 0 ≤ 2 * α * a ST.1 * b ST.2 := by positivity
      have hleft0 : 0 ≤ γ * u ST.1 * b ST.2 := by positivity
      have hright0 : 0 ≤ γ * a ST.1 * w ST.2 := by positivity
      by_cases he : ST ∈ E
      · rw [if_neg (not_not.mpr he)]
        by_cases hlargeA : γ * u ST.1 < a ST.1
        · by_cases hlargeB : γ * w ST.2 < b ST.2
          · linarith only [hgood ST hST he hlargeA hlargeB, hleft0, hright0]
          · have hsmall := mul_le_mul_of_nonneg_left (le_of_not_gt hlargeB) (ha0 ST.1)
            nlinarith only [hrough ST, hsmall, hgood0, hleft0]
        · have hsmall := mul_le_mul_of_nonneg_right (le_of_not_gt hlargeA) (hb0 ST.2)
          linarith only [hrough ST, hsmall, hgood0, hright0]
      · rw [if_pos he]
        have hareaST := mul_le_mul (hau ST.1) (hbw ST.2) (hb0 ST.2) (hu0 ST.1)
        linarith only [hrough ST, hareaST, hgood0, hleft0, hright0]
    have hsumz := hrects A B p
    have hsumab := hareas A B
    have hsumub := hareas U B
    have hsumaw := hareas A W
    have hinelig : (∑ ST ∈ P.parts.product P.parts,
        if ST ∉ E then u ST.1 * w ST.2 else 0) ≤
          (4 * γ + 9 * α + 6 / (l : ℝ)) * (n : ℝ) ^ 2 := by
      simpa only [← Finset.sum_filter, u, w] using harea
    have hAc : (A.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_card hA).trans_eq hU
    have hBc : (B.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_card hB).trans_eq hW
    calc
      _ = |∑ ST ∈ P.parts.product P.parts, (z ST - d * a ST.1 * b ST.2)| := by
        rw [Finset.sum_sub_distrib]
        simp only [mul_assoc, ← Finset.mul_sum]
        rw [show (∑ ST ∈ P.parts.product P.parts, z ST) = ∑ e ∈ A.product B, p e from hsumz]
        rw [show (∑ ST ∈ P.parts.product P.parts, a ST.1 * b ST.2) =
          (A.card : ℝ) * B.card from hsumab]
      _ ≤ ∑ ST ∈ P.parts.product P.parts, |z ST - d * a ST.1 * b ST.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ST ∈ P.parts.product P.parts,
          (2 * α * a ST.1 * b ST.2 +
          (if ST ∉ E then u ST.1 * w ST.2 else 0) +
          γ * u ST.1 * b ST.2 + γ * a ST.1 * w ST.2) := Finset.sum_le_sum hpoint
      _ = 2 * α * A.card * B.card +
          (∑ ST ∈ P.parts.product P.parts, if ST ∉ E then u ST.1 * w ST.2 else 0) +
          γ * n * B.card + γ * A.card * n := by
        simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [show (∑ ST ∈ P.parts.product P.parts, a ST.1 * b ST.2) =
            (A.card : ℝ) * B.card from hsumab,
          show (∑ ST ∈ P.parts.product P.parts, u ST.1 * b ST.2) =
            (U.card : ℝ) * B.card from hsumub,
          show (∑ ST ∈ P.parts.product P.parts, a ST.1 * w ST.2) =
            (A.card : ℝ) * W.card from hsumaw, hU, hW]
      _ ≤ _ := by
        have hleft := mul_le_mul_of_nonneg_left hBc (mul_nonneg hγ.le (Nat.cast_nonneg n))
        have hright := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAc hγ.le) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        nlinarith only [hinelig, hleft, hright]
  refine ⟨p, hp, hpne, hpout, ?_, hcoarse, ?_⟩
  · simpa only [q] using hpformula
  · intro h hh hmargin A hA B hB hlargeA hlargeB
    let K : ℝ := 6 * γ + 9 * α + 6 / (l : ℝ)
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
    have hn0 : 0 ≤ h * (n : ℝ) := mul_nonneg hh.le (Nat.cast_nonneg n)
    have hApos : 0 < (A.card : ℝ) := lt_of_le_of_lt hn0 hlargeA
    have hBpos : 0 < (B.card : ℝ) := lt_of_le_of_lt hn0 hlargeB
    have hNpos : 0 < (A.card : ℝ) * B.card := mul_pos hApos hBpos
    have hprod : h ^ 2 * (n : ℝ) ^ 2 ≤ (A.card : ℝ) * B.card := by
      have := mul_le_mul hlargeA.le hlargeB.le hn0 hApos.le
      nlinarith only [this]
    have hcancel : K / h ^ 2 * (h ^ 2 * (n : ℝ) ^ 2) = K * (n : ℝ) ^ 2 := by
      field_simp [hh2.ne']
    have herror : K * (n : ℝ) ^ 2 ≤ K / h ^ 2 * ((A.card : ℝ) * B.card) := by
      have := mul_le_mul_of_nonneg_left hprod (div_nonneg hK hh2.le)
      rwa [hcancel] at this
    have hstrict := mul_lt_mul_of_pos_right hmargin hNpos
    have hc := hcoarse A hA B hB
    change |(∑ e ∈ A.product B, p e) - d * A.card * B.card| ≤
      2 * α * A.card * B.card + K * (n : ℝ) ^ 2 at hc
    nlinarith only [hc, herror, hstrict]
