import Tablet.SuperRegularPair
import Tablet.PerfectMatching
import Mathlib.Tactic.Linarith

-- [TABLET NODE: MatchingSwitchCandidateCount]
theorem MatchingSwitchCandidateCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U W : Finset V)
    (hUW : Disjoint U W) (n : ℕ) (hn : 0 < n)
    (hU : U.card = n) (hW : W.card = n) (ε d : ENNReal)
    (hε : 0 < ε) (h4 : 4 * ε < d) (hd : d ≤ 1)
    (hSR : SuperRegularPair G U W ε d)
    (k : ℕ) (xN : Fin k → U) (yN : Fin k → W)
    (hxinj : Function.Injective xN) (hyinj : Function.Injective yN)
    (hk : (k : ENNReal) ≤ d * n / 2)
    (f : U → W) (hf : PerfectMatching G U W hUW f)
    (hN : ∀ i, f (xN i) = yN i) (x : U) (y : W) (hxy : f x = y) :
    (d.toReal - ε.toReal) * (d.toReal / 2 - ε.toReal) ^ 2 * (n : ℝ) ^ 2 ≤
      (Fintype.card {p : U × U //
        x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2 ∧
        G.Adj x (f p.1) ∧ G.Adj p.1 (f p.2) ∧ G.Adj p.2 (f x) ∧
        p.1 ∉ Set.range xN ∧ p.2 ∉ Set.range xN} : ℝ) + 3 * n := by
-- BODY
  classical
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hd
  have hεd : ε ≤ d := by
    calc
      ε = 1 * ε := (one_mul ε).symm
      _ ≤ 4 * ε := mul_le_mul_right' (by norm_num) ε
      _ ≤ d := h4.le
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top hdtop hεd
  have h4r : 4 * ε.toReal < d.toReal := by
    have hh := (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by norm_num) hεtop) hdtop).2 h4
    simpa using hh
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hder : 0 ≤ d.toReal - ε.toReal := by linarith
  have htr : 0 ≤ d.toReal / 2 - ε.toReal := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hkr : (k : ℝ) ≤ d.toReal * n / 2 := by
    have hh := (ENNReal.toReal_le_toReal (by simp)
      (ENNReal.div_ne_top (ENNReal.mul_ne_top hdtop (by simp)) (by norm_num))).2 hk
    simpa using hh
  let covered : Finset U := Finset.univ.image xN
  have hcovered : covered.card = k := by
    simp [covered, Finset.card_image_of_injective _ hxinj]
  have hcoveredR : (Finset.univ.image yN).card = k := by
    simp [Finset.card_image_of_injective _ hyinj]
  have hcoveredPartner (a : U) : f a ∈ Set.range yN ↔ a ∈ Set.range xN := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, hf.1.1 ((hN i).trans hi)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hN i).symm⟩
  let A₀ : Finset U := Finset.univ.filter fun a => G.Adj x (f a)
  let B₀ : Finset U := Finset.univ.filter fun b => G.Adj b y
  let A := A₀.filter fun a => f a ∉ Set.range yN
  let B := B₀ \ covered
  have hA (a : U) : a ∈ A ↔ G.Adj x (f a) ∧ a ∉ Set.range xN := by
    simp [A, A₀, hcoveredPartner]
  have hAsdiff : A = A₀ \ covered := by
    ext a
    simp [hA, A₀, covered]
  have hB (b : U) : b ∈ B ↔ G.Adj b y ∧ b ∉ Set.range xN := by
    simp [B, B₀, covered]
  have hA₀ : A₀.card = (W.filter fun w => G.Adj x w).card := by
    apply Finset.card_bij (fun a _ => (f a).val)
    · intro a ha
      exact Finset.mem_filter.mpr ⟨(f a).property, (Finset.mem_filter.mp ha).2⟩
    · intro a ha b hb hab
      exact hf.1.1 (Subtype.ext hab)
    · intro w hw
      let w' : W := ⟨w, (Finset.mem_filter.mp hw).1⟩
      obtain ⟨a, ha⟩ := hf.1.2 w'
      refine ⟨a, ?_, ?_⟩
      · simp [A₀, ha, w', (Finset.mem_filter.mp hw).2]
      · exact congrArg Subtype.val ha
  have hB₀ : B₀.card = (U.filter fun v => G.Adj v y).card := by
    apply Finset.card_bij (fun b _ => b.val)
    · intro b hb
      exact Finset.mem_filter.mpr ⟨b.property, (Finset.mem_filter.mp hb).2⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro b hb
      refine ⟨⟨b, (Finset.mem_filter.mp hb).1⟩, ?_, rfl⟩
      simp [B₀, (Finset.mem_filter.mp hb).2]
  have hdegreeA : (d.toReal - ε.toReal) * n ≤ (A₀.card : ℝ) := by
    have hh := (hSR.2.1 x x.property).1
    have hh' := ENNReal.toReal_mono (by simp) hh
    simpa [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hεd hdtop, hW, ← hA₀] using hh'
  have hdegreeB : (d.toReal - ε.toReal) * n ≤ (B₀.card : ℝ) := by
    have hh := (hSR.2.2 y y.property).1
    have hh' := ENNReal.toReal_mono (by simp) hh
    simpa [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hεd hdtop, hU, ← hB₀] using hh'
  have hsizeA : (d.toReal / 2 - ε.toReal) * n ≤ (A.card : ℝ) := by
    have hh : A₀.card ≤ A.card + (Finset.univ.image yN).card := by
      simpa [hAsdiff, hcovered, hcoveredR] using
        (Finset.card_le_card_sdiff_add_card (s := A₀) (t := covered))
    rw [hcoveredR] at hh
    have hh' : (A₀.card : ℝ) ≤ A.card + k := by exact_mod_cast hh
    nlinarith
  have hsizeB : (d.toReal / 2 - ε.toReal) * n ≤ (B.card : ℝ) := by
    have hh : B₀.card ≤ B.card + k := by
      simpa [B, hcovered] using
        (Finset.card_le_card_sdiff_add_card (s := B₀) (t := covered))
    have hh' : (B₀.card : ℝ) ≤ B.card + k := by exact_mod_cast hh
    nlinarith
  let L : Finset V := A.image Subtype.val
  let R : Finset V := B.image fun b => (f b).val
  have hLsub : L ⊆ U := by
    intro a ha
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha
    exact a.property
  have hRsub : R ⊆ W := by
    intro b hb
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    exact (f b).property
  have hLcard : L.card = A.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hRcard : R.card = B.card :=
    Finset.card_image_of_injective _ (Subtype.val_injective.comp hf.1.1)
  have hlargeA : ε * (U.card : ENNReal) < (L.card : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hεtop (by simp)) (by simp)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hU, hLcard]
    nlinarith
  have hlargeB : ε * (W.card : ENNReal) < (R.card : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hεtop (by simp)) (by simp)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hW, hRcard]
    nlinarith
  let edges := (L.product R).filter fun p => G.Adj p.1 p.2
  have hedge : (d.toReal - ε.toReal) * (A.card : ℝ) * B.card ≤ (edges.card : ℝ) := by
    have hh := (hSR.1 L hLsub R hRsub hlargeA hlargeB).1
    have hden : (L.card : ENNReal) * R.card ≠ 0 := by
      have hLpos : 0 < (L.card : ENNReal) := lt_of_le_of_lt bot_le hlargeA
      have hRpos : 0 < (R.card : ENNReal) := lt_of_le_of_lt bot_le hlargeB
      exact mul_ne_zero hLpos.ne' hRpos.ne'
    have hh' : (d - ε) * ((L.card : ENNReal) * R.card) ≤ (edges.card : ENNReal) := by
      exact (ENNReal.le_div_iff_mul_le (Or.inl hden)
        (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))).mp hh
    have hr := ENNReal.toReal_mono (by simp) hh'
    simpa [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hεd hdtop,
      hLcard, hRcard, mul_assoc] using hr
  let raw : Finset (U × U) := (A.product B).filter fun p => G.Adj p.1 (f p.2)
  have hraw : raw.card = edges.card := by
    apply Finset.card_bij (fun p _ => (p.1.val, (f p.2).val))
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hadj⟩
      rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p.1, ha, rfl⟩,
        Finset.mem_image.mpr ⟨p.2, hb, rfl⟩⟩, hadj⟩
    · intro p hp q hq heq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq)
      · exact hf.1.1 (Subtype.ext (congrArg Prod.snd heq))
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hadj⟩
      rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
      obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp hb
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩, ?_⟩
      · simpa [hea, heb] using hadj
      · exact Prod.ext hea heb
  have hlower : (d.toReal - ε.toReal) * (d.toReal / 2 - ε.toReal) ^ 2 * (n : ℝ) ^ 2 ≤
      (raw.card : ℝ) := by
    have hprod := mul_le_mul hsizeA hsizeB (mul_nonneg htr hnr.le) (Nat.cast_nonneg A.card)
    have hh := mul_le_mul_of_nonneg_left hprod hder
    rw [← hraw] at hedge
    nlinarith
  let D₁ : Finset (U × U) := Finset.univ.image fun b : U => (x, b)
  let D₂ : Finset (U × U) := Finset.univ.image fun a : U => (a, x)
  let D₃ : Finset (U × U) := Finset.univ.image fun a : U => (a, a)
  let bad := D₁ ∪ D₂ ∪ D₃
  have hD₁ : D₁.card = n := by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]
    simp [hU]
  have hD₂ : D₂.card = n := by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    simp [hU]
  have hD₃ : D₃.card = n := by
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    simp [hU]
  have hbad : bad.card ≤ 3 * n := by
    have hh := Finset.card_union_le (D₁ ∪ D₂) D₃
    have hh' := Finset.card_union_le D₁ D₂
    dsimp only [bad]
    omega
  let good : Finset (U × U) := Finset.univ.filter fun p =>
    x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2 ∧
    G.Adj x (f p.1) ∧ G.Adj p.1 (f p.2) ∧ G.Adj p.2 (f x) ∧
    p.1 ∉ Set.range xN ∧ p.2 ∉ Set.range xN
  have hgood : raw \ bad ⊆ good := by
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hp, hnobad⟩
    rcases Finset.mem_filter.mp hp with ⟨hp, hab⟩
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have hxa : x ≠ p.1 := by
      intro heq
      apply hnobad
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, Prod.ext heq rfl⟩
    have hxb : x ≠ p.2 := by
      intro heq
      apply hnobad
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl heq⟩
    have hab' : p.1 ≠ p.2 := by
      intro heq
      apply hnobad
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl heq⟩
    rcases (hA p.1).mp ha with ⟨hax, haN⟩
    rcases (hB p.2).mp hb with ⟨hby, hbN⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa, hxb, hab', hax, hab,
      hxy.symm ▸ hby, haN, hbN⟩
  have hcount : raw.card ≤ good.card + 3 * n := by
    have hh := Finset.card_le_card_sdiff_add_card (s := raw) (t := bad)
    have hh' := Finset.card_le_card hgood
    omega
  have hcountR : (raw.card : ℝ) ≤ good.card + 3 * n := by exact_mod_cast hcount
  have hgoodcard : good.card = Fintype.card {p : U × U //
      x ≠ p.1 ∧ x ≠ p.2 ∧ p.1 ≠ p.2 ∧
      G.Adj x (f p.1) ∧ G.Adj p.1 (f p.2) ∧ G.Adj p.2 (f x) ∧
      p.1 ∉ Set.range xN ∧ p.2 ∉ Set.range xN} := by
    simp [good, Fintype.card_subtype]
  rw [hgoodcard] at hcountR
  exact hlower.trans hcountR
