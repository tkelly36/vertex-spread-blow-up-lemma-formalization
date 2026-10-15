import Tablet.SuperRegularSubgraph
import Tablet.CompleteRowPadding
import Tablet.LowerSuperRegularPairEmbedding
import Tablet.SuperRegularPairEmbedding
import Tablet.SuperRegularPairOneVertexDeletion

universe u v

-- [TABLET NODE: NearEqualSuperRegularExtraction]
theorem NearEqualSuperRegularExtraction (η c d : ENNReal)
    (hη : 0 < η) (hη1 : η < 1) (hc : 0 < c)
    (hcd : c < d ^ 2 / 2) (hd1 : d ≤ 1) :
    ∃ θ : ENNReal, ∃ N : ℕ, 0 < θ ∧ θ < η ∧ 1 ≤ N ∧
      (∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (m : ℕ),
        N ≤ m → Disjoint U W →
        (U.card = m ∨ U.card = m + 1) →
        (W.card = m ∨ W.card = m + 1) →
        LowerSuperRegularPair G U W θ d →
        ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
          F ≤ G ∧
          (∀ ⦃u v⦄, F.Adj u v →
            (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U)) ∧
          SuperRegularPair F U W η c) ∧
      (∀ {V : Type v} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V) (m : ℕ),
        N ≤ m → Disjoint U W →
        (U.card = m ∨ U.card = m + 1) →
        (W.card = m ∨ W.card = m + 1) →
        LowerSuperRegularPair G U W θ d →
        ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
          F ≤ G ∧
          (∀ ⦃u v⦄, F.Adj u v →
            (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U)) ∧
          SuperRegularPair F U W η c) := by
-- BODY
  classical
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd1
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top (by finiteness : d ^ 2 / 2 ≠ ⊤) hcd.le
  have hηtop : η ≠ ⊤ := ne_top_of_lt hη1
  have hrη : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  have hrη1 : η.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hηtop (by simp)).mpr hη1
  have hrc : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hctop
  have hrd1 : d.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hdtop (by simp)).mpr hd1
  have hrcd : c.toReal < d.toReal ^ 2 / 2 := by
    have hh := (ENNReal.toReal_lt_toReal hctop (by finiteness)).mpr hcd
    simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using hh
  have hrd : 0 < d.toReal := by
    nlinarith only [hrcd, hrc, ENNReal.toReal_nonneg (a := d)]
  let q : ℝ := Real.sqrt (2 * c.toReal)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = 2 * c.toReal := Real.sq_sqrt (by positivity)
  have hqd : q < d.toReal := by nlinarith only [hq2, hrcd, hrd, hq]
  have hq1 : q < 1 := hqd.trans_le hrd1
  have hrc1 : c.toReal ≤ 1 := by nlinarith only [hrcd, hrd1, hrd]
  let τ : ℝ := η.toReal / 4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ < 1 := by dsimp [τ]; linarith
  obtain ⟨αu, Nu, hαu, hαuτ, hexu⟩ :=
    SuperRegularSubgraph.{u} (ENNReal.ofReal τ) (ENNReal.ofReal q)
      (ENNReal.ofReal_pos.mpr hτ) (ENNReal.ofReal_lt_one.mpr hτ1)
      (ENNReal.ofReal_pos.mpr hq) (ENNReal.ofReal_lt_one.mpr hq1)
  obtain ⟨αv, Nv, hαv, hαvτ, hexv⟩ :=
    SuperRegularSubgraph.{v} (ENNReal.ofReal τ) (ENNReal.ofReal q)
      (ENNReal.ofReal_pos.mpr hτ) (ENNReal.ofReal_lt_one.mpr hτ1)
      (ENNReal.ofReal_pos.mpr hq) (ENNReal.ofReal_lt_one.mpr hq1)
  have hαutop : αu ≠ ⊤ := ne_top_of_lt hαuτ
  have hαvtop : αv ≠ ⊤ := ne_top_of_lt hαvτ
  have hαur : 0 < αu.toReal := ENNReal.toReal_pos hαu.ne' hαutop
  have hαvr : 0 < αv.toReal := ENNReal.toReal_pos hαv.ne' hαvtop
  let β : ℝ := min αu.toReal (min αv.toReal (min ((d.toReal - q) / 4) (1 / 2)))
  have hβ : 0 < β := by
    have hgap : 0 < (d.toReal - q) / 4 := div_pos (sub_pos.mpr hqd) (by norm_num)
    exact lt_min hαur (lt_min hαvr (lt_min hgap (by norm_num)))
  have hβu : ENNReal.ofReal β ≤ αu := by
    rw [← ENNReal.ofReal_toReal hαutop]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hβv : ENNReal.ofReal β ≤ αv := by
    rw [← ENNReal.ofReal_toReal hαvtop]
    exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))
  have hβgap : β ≤ (d.toReal - q) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hβhalf : β ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hβ1 : ENNReal.ofReal β ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (by linarith : β ≤ 1)
  have hqβd : ENNReal.ofReal q ≤ d - ENNReal.ofReal β := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (ENNReal.sub_ne_top hdtop)).mp
    have hβd : ENNReal.ofReal β ≤ d := by
      rw [← ENNReal.ofReal_toReal hdtop]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    simp only [ENNReal.toReal_ofReal hq.le, ENNReal.toReal_sub_of_le hβd hdtop,
      ENNReal.toReal_ofReal hβ.le]
    linarith only [hβgap, hqd]
  let θr : ℝ := min (η.toReal / 2) (β * β / 2)
  have hθr : 0 < θr := by dsimp [θr]; positivity
  have hθη : ENNReal.ofReal θr < η := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hθr.le hηtop).mpr
    have := min_le_left (η.toReal / 2) (β * β / 2)
    dsimp [θr]
    linarith
  have hθbudget : ENNReal.ofReal θr ≤ ENNReal.ofReal β * ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_mul hβ.le]
    apply ENNReal.ofReal_le_ofReal
    have := min_le_right (η.toReal / 2) (β * β / 2)
    dsimp [θr]
    nlinarith only [this, hβ.le]
  obtain ⟨M, hM⟩ := exists_nat_gt (8 / η.toReal)
  let N := max 1 (max Nu (max Nv M))
  have hN1 : 1 ≤ N := le_max_left _ _
  have hNu : Nu ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNv : Nv ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNM : M ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hqc : (ENNReal.ofReal q) ^ 2 / 2 = c := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) hctop).mp
    simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofNat]
    linarith only [hq2]
  refine ⟨ENNReal.ofReal θr, N, ENNReal.ofReal_pos.mpr hθr, hθη, hN1, ?_, ?_⟩
  all_goals
    intro V _ _ G _ U W m hNm hUW hU hW hlow
    have hm : 1 ≤ m := hN1.trans hNm
    have hfloor : 4 ≤ η.toReal * (m : ℝ) := by
      have hMm : (M : ℝ) ≤ m := by exact_mod_cast hNM.trans hNm
      have hh : 8 < (m : ℝ) * η.toReal := (div_lt_iff₀ hrη).mp (hM.trans_le hMm)
      linarith only [hh]
    have densitySwap (K : SimpleGraph V) [DecidableRel K.Adj] (S T : Finset V) :
        PairDensity K S T = PairDensity K T S := by
      have hcount :
          ((S.product T).filter fun p => K.Adj p.1 p.2).card =
          ((T.product S).filter fun p => K.Adj p.1 p.2).card := by
        apply Finset.card_bij (fun p _ => p.swap)
        · intro p hp
          obtain ⟨hpST, hpAdj⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpS, hpT⟩ := Finset.mem_product.mp hpST
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hpT, hpS⟩, K.symm hpAdj⟩
        · intro p _ q _ hpq
          exact Prod.swap_injective hpq
        · intro p hp
          obtain ⟨hpTS, hpAdj⟩ := Finset.mem_filter.mp hp
          obtain ⟨hpT, hpS⟩ := Finset.mem_product.mp hpTS
          exact ⟨p.swap, Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hpS, hpT⟩, K.symm hpAdj⟩, rfl⟩
      simp only [PairDensity, hcount, mul_comm]
    have lowSwap (L R : Finset V)
        (h : LowerSuperRegularPair G L R (ENNReal.ofReal θr) d) :
        LowerSuperRegularPair G R L (ENNReal.ofReal θr) d := by
      refine ⟨?_, ?_, ?_⟩
      · intro S hS T hT hScard hTcard
        simpa only [densitySwap G S T] using h.1 T hT S hS hTcard hScard
      · intro w hw
        simpa only [G.adj_comm] using h.2.2 w hw
      · intro u hu
        simpa only [G.adj_comm] using h.2.1 u hu
    have highSwap (K : SimpleGraph V) [DecidableRel K.Adj] (L R : Finset V)
        (h : SuperRegularPair K L R η c) : SuperRegularPair K R L η c := by
      refine ⟨?_, ?_, ?_⟩
      · intro S hS T hT hScard hTcard
        simpa only [densitySwap K S T] using h.1 T hT S hS hTcard hScard
      · intro w hw
        simpa only [K.adj_comm] using h.2.2 w hw
      · intro u hu
        simpa only [K.adj_comm] using h.2.1 u hu
    have ordered : ∀ (L R : Finset V), Disjoint L R →
        (L.card = m ∨ L.card = m + 1) → (R.card = m ∨ R.card = m + 1) →
        L.card ≤ R.card → LowerSuperRegularPair G L R (ENNReal.ofReal θr) d →
        ∃ F : SimpleGraph V, ∃ _ : DecidableRel F.Adj,
          F ≤ G ∧ (∀ ⦃x y⦄, F.Adj x y →
            (x ∈ L ∧ y ∈ R) ∨ (x ∈ R ∧ y ∈ L)) ∧
          SuperRegularPair F L R η c := by
      intro L R hLR hL hR hle hlowLR
      -- Keep only crossing edges and pad the smaller part when necessary.
      let e : V ↪ Option V := ⟨Option.some, Option.some_injective V⟩
      let D : Finset (Option V) := if L.card < R.card then {none} else ∅
      let Lp := (L.map e) ∪ D
      let Rp := R.map e
      let Gp : SimpleGraph (Option V) := {
        Adj := fun x y => match x, y with
          | some x, some y => G.Adj x y ∧
              ((x ∈ L ∧ y ∈ R) ∨ (x ∈ R ∧ y ∈ L))
          | none, some y => L.card < R.card ∧ y ∈ R
          | some x, none => L.card < R.card ∧ x ∈ R
          | none, none => False
        symm := by
          intro x y hxy
          cases x with
          | none => cases y with
            | none => exact hxy
            | some y => exact hxy
          | some x =>
            cases y with
            | none => exact hxy
            | some y =>
              exact ⟨G.symm hxy.1, hxy.2.elim
                (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩
        loopless := ⟨by intro x; cases x <;> simp⟩ }
      letI : DecidableRel Gp.Adj := Classical.decRel _
      have hD : Disjoint (L.map e) D := by
        dsimp [D]
        split_ifs <;> simp [e]
      have hLp : Lp.card = R.card := by
        have hnear : R.card ≤ L.card + 1 := by omega
        dsimp [Lp]
        rw [Finset.card_union_of_disjoint hD, Finset.card_map]
        dsimp [D]
        split_ifs with hlt
        · simp only [Finset.card_singleton]; omega
        · simp only [Finset.card_empty, add_zero]; omega
      have hRp : Rp.card = R.card := Finset.card_map _
      have hcopy : ∀ x ∈ L, ∀ y ∈ R, Gp.Adj (e x) (e y) ↔ G.Adj x y := by
        intro x hx y hy
        change (G.Adj x y ∧ _) ↔ G.Adj x y
        exact and_iff_left (Or.inl ⟨hx, hy⟩)
      have hcomplete : ∀ z ∈ D, ∀ y ∈ R, Gp.Adj z (e y) := by
        intro z hz y hy
        dsimp [D] at hz
        split_ifs at hz with hlt
        · have hz0 : z = none := Finset.mem_singleton.mp hz
          subst z
          exact ⟨hlt, hy⟩
        · simp at hz
      have hpad : LowerSuperRegularPair Gp Lp Rp (ENNReal.ofReal β) d :=
        CompleteRowPadding G Gp e L R D (ENNReal.ofReal θr) (ENNReal.ofReal β) d
          (ENNReal.ofReal_pos.mpr hθr) hθbudget hβ1 hd1 hD hLp hcopy hcomplete hlowLR
      have hdis : Disjoint Lp Rp := by
        apply Finset.disjoint_left.mpr
        intro z hzL hzR
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hzR
        rcases Finset.mem_union.mp hzL with hz | hz
        · obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hz
          have heq : x = y := e.injective hxy
          exact Finset.disjoint_left.mp hLR (heq ▸ hx) hy
        · dsimp [D] at hz
          split_ifs at hz <;> simp [e] at hz
      have hsupport : ∀ ⦃x y⦄, Gp.Adj x y →
          (x ∈ Lp ∧ y ∈ Rp) ∨ (x ∈ Rp ∧ y ∈ Lp) := by
        intro x y hxy
        cases x with
        | none =>
          cases y with
          | none => exact False.elim hxy
          | some y =>
            exact Or.inl ⟨Finset.mem_union_right _ (by simp [D, hxy.1]),
              Finset.mem_map.mpr ⟨y, hxy.2, rfl⟩⟩
        | some x =>
          cases y with
          | none =>
            exact Or.inr ⟨Finset.mem_map.mpr ⟨x, hxy.2, rfl⟩,
              Finset.mem_union_right _ (by simp [D, hxy.1])⟩
          | some y =>
            rcases hxy.2 with hh | hh
            · exact Or.inl ⟨Finset.mem_union_left _ (Finset.mem_map.mpr ⟨x, hh.1, rfl⟩),
                Finset.mem_map.mpr ⟨y, hh.2, rfl⟩⟩
            · exact Or.inr ⟨Finset.mem_map.mpr ⟨x, hh.1, rfl⟩,
                Finset.mem_union_left _ (Finset.mem_map.mpr ⟨y, hh.2, rfl⟩)⟩
      -- Extraction requires the two parts to cover its vertex type.
      let S := {z : Option V // z ∈ Lp ∪ Rp}
      let Ls : Finset S := Finset.univ.filter fun z => z.val ∈ Lp
      let Rs : Finset S := Finset.univ.filter fun z => z.val ∈ Rp
      let Gs : SimpleGraph S := Gp.comap Subtype.val
      letI : DecidableRel Gs.Adj := Classical.decRel _
      have images (T : Finset (Option V)) (hT : T ⊆ Lp ∪ Rp) :
          (Finset.univ.filter fun z : S => z.val ∈ T).image Subtype.val = T := by
        ext z
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hz
          exact ⟨⟨z, hT hz⟩, hz, rfl⟩
      have hLs : Ls.image Subtype.val = Lp := images Lp Finset.subset_union_left
      have hRs : Rs.image Subtype.val = Rp := images Rp Finset.subset_union_right
      have hLc : Ls.card = R.card := by
        rw [← hLp, ← hLs, Finset.card_image_of_injective _ Subtype.val_injective]
      have hRc : Rs.card = R.card := by
        rw [← hRp, ← hRs, Finset.card_image_of_injective _ Subtype.val_injective]
      have hdisS : Disjoint Ls Rs := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        exact Finset.disjoint_left.mp hdis (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      have hcoverS : Ls ∪ Rs = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro x
        simpa only [Ls, Rs, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and] using x.property
      have hsupportS : ∀ ⦃x y⦄, Gs.Adj x y →
          (x ∈ Ls ∧ y ∈ Rs) ∨ (x ∈ Rs ∧ y ∈ Ls) := by
        intro x y hxy
        simpa only [Ls, Rs, Finset.mem_filter, Finset.mem_univ, true_and]
          using hsupport hxy
      have hlowS : LowerSuperRegularPair Gs Ls Rs (ENNReal.ofReal β) d := by
        apply (LowerSuperRegularPairEmbedding Subtype.val Subtype.val_injective Gs Gp
          Ls Rs (ENNReal.ofReal β) d (fun _ _ _ _ => Iff.rfl)).mpr
        simpa only [hLs, hRs] using hpad
      have extractionInput (α : ENNReal) (hαtop : α ≠ ⊤) (hβα : ENNReal.ofReal β ≤ α) :
          LowerSuperRegularPair Gs Ls Rs α (ENNReal.ofReal q + α) := by
        have hend : ENNReal.ofReal q + α - α = ENNReal.ofReal q :=
          ENNReal.add_sub_cancel_right hαtop
        refine ⟨?_, ?_, ?_⟩
        · intro A hA B hB hsizeA hsizeB
          rw [hend]
          exact hqβd.trans (hlowS.1 A hA B hB
            ((mul_le_mul_left hβα _).trans_lt hsizeA)
            ((mul_le_mul_left hβα _).trans_lt hsizeB))
        · intro x hx
          rw [hend]
          exact (mul_le_mul_left hqβd _).trans (hlowS.2.1 x hx)
        · intro y hy
          rw [hend]
          exact (mul_le_mul_left hqβd _).trans (hlowS.2.2 y hy)
      have hRm : m ≤ R.card := by omega
      have hextracted : ∃ F : SimpleGraph S, ∃ _ : DecidableRel F.Adj,
          F ≤ Gs ∧ SuperRegularPair F Ls Rs (ENNReal.ofReal τ) c := by
        rw [← hqc]
        first
        | exact hexu Gs Ls Rs R.card (hNu.trans (hNm.trans hRm)) hLc hRc
            hdisS hcoverS hsupportS (extractionInput αu hαutop hβu)
        | exact hexv Gs Ls Rs R.card (hNv.trans (hNm.trans hRm)) hLc hRc
            hdisS hcoverS hsupportS (extractionInput αv hαvtop hβv)
      obtain ⟨Fs, hFsdec, hFsGs, hFsreg⟩ := hextracted
      letI : DecidableRel Fs.Adj := hFsdec
      let inc : S ↪ Option V := ⟨Subtype.val, Subtype.val_injective⟩
      let Fp := Fs.map inc
      letI : DecidableRel Fp.Adj := Classical.decRel _
      have hFpGp : Fp ≤ Gp := (SimpleGraph.map_le_iff_le_comap inc Fs Gp).mpr hFsGs
      have hFpReg : SuperRegularPair Fp Lp Rp (ENNReal.ofReal τ) c := by
        have hh := SuperRegularPairEmbedding inc inc.injective Fs Fp Ls Rs
          (ENNReal.ofReal τ) c (fun _ _ _ _ => SimpleGraph.map_adj_apply) hFsreg
        change SuperRegularPair Fp (Ls.image Subtype.val) (Rs.image Subtype.val)
          (ENNReal.ofReal τ) c at hh
        simpa only [hLs, hRs] using hh
      have hdelete : SuperRegularPair Fp (L.map e) (R.map e) η c := by
        have hh := SuperRegularPairOneVertexDeletion Fp Lp Rp (L.map e) (R.map e)
          m τ η.toReal c.toReal hτ.le hrη hrη1.le hrc.le hrc1
          (by dsimp [τ]; linarith) hm hfloor
          Finset.subset_union_left (by rfl)
          (by simpa only [Finset.card_map] using (show m ≤ L.card by omega))
          (by simpa only [Finset.card_map] using hRm)
          (by rw [hLp, Finset.card_map]; omega)
          (by change Rp.card ≤ Rp.card + 1; omega)
          (by simpa only [ENNReal.ofReal_toReal hctop] using hFpReg)
        simpa only [ENNReal.ofReal_toReal hηtop, ENNReal.ofReal_toReal hctop] using hh
      -- Pulling back along `some` removes the dummy and isolates the ambient remainder.
      let F := Fp.comap e
      letI : DecidableRel F.Adj := Classical.decRel _
      have hFG : F ≤ G := by
        intro x y hxy
        have hh := hFpGp hxy
        exact hh.1
      have hFsupport : ∀ ⦃x y⦄, F.Adj x y →
          (x ∈ L ∧ y ∈ R) ∨ (x ∈ R ∧ y ∈ L) := by
        intro x y hxy
        exact (hFpGp hxy).2
      have density (A B : Finset V) :
          PairDensity Fp (A.map e) (B.map e) = PairDensity F A B := by
        unfold PairDensity
        simp only [Finset.product_eq_sprod]
        rw [← Finset.prodMap_map_product, Finset.filter_map, Finset.card_map,
          Finset.card_map, Finset.card_map]
        rfl
      have countLeft (x : V) :
          ((R.map e).filter fun y => Fp.Adj (e x) y).card =
          (R.filter fun y => F.Adj x y).card := by
        rw [Finset.filter_map, Finset.card_map]
        rfl
      have countRight (y : V) :
          ((L.map e).filter fun x => Fp.Adj x (e y)).card =
          (L.filter fun x => F.Adj x y).card := by
        rw [Finset.filter_map, Finset.card_map]
        rfl
      refine ⟨F, inferInstance, hFG, hFsupport, ?_, ?_, ?_⟩
      · intro A hA B hB hsizeA hsizeB
        have hh := hdelete.1 (A.map e) (Finset.map_subset_map.mpr hA)
          (B.map e) (Finset.map_subset_map.mpr hB)
          (by simpa only [Finset.card_map] using hsizeA)
          (by simpa only [Finset.card_map] using hsizeB)
        simpa only [density] using hh
      · intro x hx
        have hh := hdelete.2.1 (e x) (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
        simpa only [Finset.card_map, countLeft] using hh
      · intro y hy
        have hh := hdelete.2.2 (e y) (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
        simpa only [Finset.card_map, countRight] using hh
    rcases le_total U.card W.card with hle | hle
    · exact ordered U W hUW hU hW hle hlow
    · obtain ⟨F, hFdec, hFG, hFsupport, hFreg⟩ :=
        ordered W U hUW.symm hW hU hle (lowSwap U W hlow)
      letI : DecidableRel F.Adj := hFdec
      exact ⟨F, hFdec, hFG, fun _ _ h => (hFsupport h).elim Or.inr Or.inl,
        highSwap F W U hFreg⟩
