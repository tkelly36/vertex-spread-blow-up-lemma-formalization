import Tablet.BlowUpInstance
import Tablet.CandidacySystem
import Tablet.CandidacyLowerSuperRegular
import Tablet.CapacityPreservingReassignment
import Tablet.FilteredProductRowCount

open scoped Classical symmDiff

-- [TABLET NODE: HostExceptionalCorrection]
theorem HostExceptionalCorrection {r k : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (σ : VH → Fin r × Fin k) (f : VG → Fin r × Fin k)
    (ε d : ENNReal) (n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hε : 0 < ε) (hεsmall : ε < 1 / (8 * (k : ENNReal) ^ 2)) (hd : d ≤ 1)
    (hσ : ∀ x, (σ x).1 = B.sourceCluster x)
    (hf : ∀ v, (f v).1 = B.hostCluster v)
    (hcard : ∀ i,
      (Finset.univ.filter fun x => B.sourceCluster x = i).card = n ∧
      (Finset.univ.filter fun v => B.hostCluster v = i).card = n)
    (hsize : ∀ p, (Finset.univ.filter fun x => σ x = p).card = n / k ∨
      (Finset.univ.filter fun x => σ x = p).card = n / k + 1)
    (hcapacity : ∀ p, (Finset.univ.filter fun v => f v = p).card =
      (Finset.univ.filter fun x => σ x = p).card)
    (hcand : CandidacyLowerSuperRegular B A ε d) :
    ∃ f' : VG → Fin r × Fin k,
      (∀ v, (f' v).1 = B.hostCluster v) ∧
      (∀ p, (Finset.univ.filter fun v => f' v = p).card =
        (Finset.univ.filter fun x => σ x = p).card) ∧
      (∀ p, (((Finset.univ.filter fun v => f' v = p) ∆
          (Finset.univ.filter fun v => f v = p)).card : ENNReal) ≤
        2 * k * ε * n) ∧
      (∀ v, (d - 2 * ε) *
        ((Finset.univ.filter fun x => σ x = f' v).card : ENNReal) ≤
        ((Finset.univ.filter fun x => σ x = f' v ∧ A.allowed x v).card : ENNReal)) := by
-- BODY
  classical
  by_cases htrivial : d ≤ 2 * ε
  · refine ⟨f, hf, hcapacity, ?_, ?_⟩
    · intro p
      simp
    · intro v
      simp [tsub_eq_zero_of_le htrivial]
  have hkpos : 0 < k := by omega
  have hmpos : 0 < n / k := Nat.div_pos (by omega) hkpos
  have hεfinite : ε ≠ ⊤ := ne_top_of_lt hεsmall
  have htwo : ε ≤ 2 * ε := by
    simpa using mul_le_mul_left (show (1 : ENNReal) ≤ 2 by norm_num) ε
  -- The floor estimate leaves room for the union of all exceptional sets.
  have hroom : (k : ENNReal) * ε * n < (n / k : ℕ) := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmR : (1 : ℝ) ≤ (n / k : ℕ) := by exact_mod_cast hmpos
    have hfloor : (n : ℝ) < (k : ℝ) * ((n / k : ℕ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ n hkpos
    have heR : ε.toReal < 1 / (8 * (k : ℝ) ^ 2) := by
      have h := (ENNReal.toReal_lt_toReal hεfinite
        (by finiteness : 1 / (8 * (k : ENNReal) ^ 2) ≠ ⊤)).mpr hεsmall
      simpa using h
    have heprod : ε.toReal * (8 * (k : ℝ) ^ 2) < 1 :=
      (lt_div_iff₀ (by positivity)).mp heR
    have hnk : (n : ℝ) ≤ 2 * (k : ℝ) * (n / k : ℕ) := by nlinarith
    have hmain : (k : ℝ) * ε.toReal * n < (n / k : ℕ) := by
      have hscaled := mul_le_mul_of_nonneg_left hnk
        (show 0 ≤ (k : ℝ) * ε.toReal by positivity)
      have hscaled' := mul_lt_mul_of_pos_right heprod
        (show 0 < (n / k : ℕ) / (4 : ℝ) by positivity)
      nlinarith [ENNReal.toReal_nonneg (a := ε)]
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by simp)).mp
    simpa using hmain
  let X (p : Fin r × Fin k) := Finset.univ.filter fun x => σ x = p
  let S (i : Fin r) := Finset.univ.filter fun x => B.sourceCluster x = i
  let V (i : Fin r) := Finset.univ.filter fun v => B.hostCluster v = i
  have hXmin (p : Fin r × Fin k) : n / k ≤ (X p).card := by
    rcases hsize p with h | h <;> change n / k ≤
      (Finset.univ.filter fun x => σ x = p).card <;> omega
  have hlarge (p : Fin r × Fin k) : ε * n < (X p).card := by
    calc
      ε * n = 1 * ε * n := by simp
      _ ≤ (k : ENNReal) * ε * n :=
        mul_le_mul_left (mul_le_mul_left
          (show (1 : ENNReal) ≤ k by exact_mod_cast hk) ε) n
      _ < (n / k : ℕ) := hroom
      _ ≤ (X p).card := by exact_mod_cast hXmin p
  let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun p q =>
    ∃ x : VH, ∃ v : VG, p = Sum.inl x ∧ q = Sum.inr v ∧ A.allowed x v
  letI : DecidableRel C.Adj := Classical.decRel _
  let left (T : Finset VH) : Finset (VH ⊕ VG) := T.map Function.Embedding.inl
  let right (T : Finset VG) : Finset (VH ⊕ VG) := T.map Function.Embedding.inr
  have hadj (x : VH) (v : VG) : C.Adj (Sum.inl x) (Sum.inr v) ↔ A.allowed x v := by
    simp [C, SimpleGraph.fromRel_adj]
  have hadj' (v : VG) (x : VH) : C.Adj (Sum.inr v) (Sum.inl x) ↔ A.allowed x v := by
    rw [C.adj_comm, hadj]
  have hleft (T : Finset VH) (v : VG) :
      ((left T).filter fun z => C.Adj z (Sum.inr v)).card =
        (T.filter fun x => A.allowed x v).card := by
    simp only [left, Finset.filter_map, Finset.card_map, Function.comp_def,
      Function.Embedding.inl_apply, hadj]
  have hleft' (T : Finset VH) (v : VG) :
      ((left T).filter fun z => C.Adj (Sum.inr v) z).card =
        (T.filter fun x => A.allowed x v).card := by
    simp only [left, Finset.filter_map, Finset.card_map, Function.comp_def,
      Function.Embedding.inl_apply, hadj']
  have hpair (i : Fin r) : LowerSuperRegularPair C (left (S i)) (right (V i)) ε d := by
    have hl : left (S i) = Finset.univ.filter (fun z : VH ⊕ VG =>
        ∃ x : VH, z = Sum.inl x ∧ B.sourceCluster x = i) := by
      ext z
      cases z <;> simp [left, S]
    have hr : right (V i) = Finset.univ.filter (fun z : VH ⊕ VG =>
        ∃ v : VG, z = Sum.inr v ∧ B.hostCluster v = i) := by
      ext z
      cases z <;> simp [right, V]
    rw [hl, hr]
    exact hcand i
  have hXsub (i : Fin r) (j : Fin k) : X (i, j) ⊆ S i := by
    intro x hx
    have h := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    simpa [S, hσ] using h
  -- Only the lower density test is used; no full-regularity tail lemma is needed.
  have honeSided : ∀ (L Q T : Finset (VH ⊕ VG)),
      LowerRegularPair C L Q ε d → T ⊆ L → ε * L.card < T.card →
      (((Q.filter fun v => ((T.filter fun x => C.Adj v x).card : ENNReal) <
        (d - 2 * ε) * T.card).card : ENNReal)) ≤ ε * Q.card := by
    intro L Q T hreg hTL hTsize
    let W := Q.filter fun v => ((T.filter fun x => C.Adj v x).card : ENNReal) <
      (d - 2 * ε) * T.card
    change (W.card : ENNReal) ≤ ε * Q.card
    by_contra hbound
    have hWsize : ε * Q.card < W.card := lt_of_not_ge hbound
    have hWzero : (W.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hWsize)
    have hTzero : (T.card : ENNReal) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hTsize)
    have hWnonempty : W.Nonempty := Finset.card_pos.mp (by exact_mod_cast
      ((zero_le _).trans_lt hWsize : (0 : ENNReal) < W.card))
    have hsum : (∑ v ∈ W, ((T.filter fun x => C.Adj v x).card : ENNReal)) <
        ∑ _v ∈ W, (d - 2 * ε) * T.card := by
      apply ENNReal.sum_lt_sum_of_nonempty hWnonempty
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    have htranspose : ((T.product W).filter fun p => C.Adj p.1 p.2).card =
        ((W.product T).filter fun p => C.Adj p.1 p.2).card := by
      apply Finset.card_bij (fun p _ => (p.2, p.1))
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, ha⟩
        rcases Finset.mem_product.mp hp with ⟨hx, hv⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hx⟩, ha.symm⟩
      · intro p _ q _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, ha⟩
        rcases Finset.mem_product.mp hp with ⟨hv, hx⟩
        exact ⟨(p.2, p.1), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hx, hv⟩, ha.symm⟩, rfl⟩
    have hdensity : PairDensity C T W < d - 2 * ε := by
      unfold PairDensity
      apply (ENNReal.div_lt_iff (Or.inl (mul_ne_zero hTzero hWzero))
        (Or.inl (by finiteness))).mpr
      rw [htranspose, FilteredProductRowCount W T C.Adj]
      simpa only [Nat.cast_sum, Finset.sum_const, nsmul_eq_mul, mul_assoc,
        mul_comm, mul_left_comm] using hsum
    exact (not_lt_of_ge (hreg T hTL W (Finset.filter_subset _ _) hTsize hWsize))
      (hdensity.trans_le (tsub_le_tsub_left htwo d))
  let Ebin (i : Fin r) (j : Fin k) := (V i).filter fun v =>
    (((X (i, j)).filter fun x => A.allowed x v).card : ENNReal) <
      (d - 2 * ε) * (X (i, j)).card
  have hEbin (i : Fin r) (j : Fin k) : ((Ebin i j).card : ENNReal) ≤ ε * n := by
    have hbad := honeSided (left (S i)) (right (V i)) (left (X (i, j)))
      (hpair i).1 (Finset.map_subset_map.mpr (hXsub i j)) (by
        simpa [left, S, (hcard i).1] using hlarge (i, j))
    simpa only [right, Finset.filter_map, Finset.card_map, Function.comp_def,
      Function.Embedding.inr_apply, hleft', left, Ebin,
      Function.Embedding.inl_apply, hadj',
      show (V i).card = n from (hcard i).2] using hbad
  let E (i : Fin r) := Finset.univ.biUnion (Ebin i)
  have hES (i : Fin r) : E i ⊆ V i := by
    intro v hv
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hj).1
  have hEbound (i : Fin r) : ((E i).card : ENNReal) ≤ (k : ENNReal) * ε * n := by
    calc
      ((E i).card : ENNReal) ≤ ∑ j : Fin k, ((Ebin i j).card : ENNReal) := by
        exact_mod_cast (Finset.card_biUnion_le : (E i).card ≤ ∑ j : Fin k, (Ebin i j).card)
      _ ≤ ∑ _j : Fin k, ε * n := Finset.sum_le_sum fun j _ => hEbin i j
      _ = (k : ENNReal) * ε * n := by simp [mul_assoc]
  have hpartition (i : Fin r) (P : VH → Prop) [DecidablePred P] :
      ∑ j : Fin k, ((X (i, j)).filter P).card = ((S i).filter P).card := by
    have htest (j : Fin k) : (((S i).filter P).filter fun x => (σ x).2 = j) =
        (X (i, j)).filter P := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, X]
      rw [Prod.ext_iff]
      simp only [hσ]
      tauto
    simpa only [htest, Finset.mem_univ, Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter ((S i).filter P) Finset.univ
        (fun x => (σ x).2)
  have hsuitable (i : Fin r) (v : VG) (hv : v ∈ V i) : ∃ j : Fin k,
      (d - ε) * (X (i, j)).card ≤
        (((X (i, j)).filter fun x => A.allowed x v).card : ENNReal) := by
    have hdegree := (hpair i).2.2 (Sum.inr v) (by simpa [right] using hv)
    rw [hleft] at hdegree
    have hsumX : ∑ j : Fin k, (X (i, j)).card = n := by
      simpa only [Finset.filter_true, show (S i).card = n from (hcard i).1] using
        hpartition i (fun _ => True)
    have hsumN := hpartition i (fun x => A.allowed x v)
    by_contra hnone
    have hstrict (j : Fin k) :
        (((X (i, j)).filter fun x => A.allowed x v).card : ENNReal) <
          (d - ε) * (X (i, j)).card := by
      exact lt_of_not_ge (fun h => hnone ⟨j, h⟩)
    have hnonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
      ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
    have hsum := ENNReal.sum_lt_sum_of_nonempty hnonempty (fun j _ => hstrict j)
    have hsumXC : (∑ j : Fin k, ((X (i, j)).card : ENNReal)) = n := by
      exact_mod_cast hsumX
    rw [← Finset.mul_sum, hsumXC, ← Nat.cast_sum, hsumN] at hsum
    exact (not_lt_of_ge (by simpa [left, S, (hcard i).1] using hdegree)) hsum
  have hcorrect (i : Fin r) : ∃ g : VG → Fin k,
      (∀ v ∈ E i, (d - ε) * (X (i, g v)).card ≤
        (((X (i, g v)).filter fun x => A.allowed x v).card : ENNReal)) ∧
      (∀ j, ((V i).filter fun v => g v = j).card = (X (i, j)).card) ∧
      (∀ j, ((((V i).filter fun v => g v = j) ∆
        ((V i).filter fun v => (f v).2 = j)).card : ENNReal) ≤ 2 * k * ε * n) := by
    let b : VG → Fin k := fun v =>
      if hv : v ∈ V i then (hsuitable i v hv).choose else ⟨0, hkpos⟩
    have hb (v : VG) (hv : v ∈ V i) : (d - ε) * (X (i, b v)).card ≤
        (((X (i, b v)).filter fun x => A.allowed x v).card : ENNReal) := by
      simpa only [b, dif_pos hv] using (hsuitable i v hv).choose_spec
    have holdcard (j : Fin k) : ((V i).filter fun v => (f v).2 = j).card =
        (X (i, j)).card := by
      have heq : ((V i).filter fun v => (f v).2 = j) =
          Finset.univ.filter fun v => f v = (i, j) := by
        ext v
        simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Prod.ext_iff]
        simp only [hf]
      rw [heq]
      exact hcapacity (i, j)
    have hroom' (j : Fin k) : (E i).card < ((V i).filter fun v => (f v).2 = j).card := by
      rw [holdcard]
      exact_mod_cast ((hEbound i).trans_lt (hroom.trans_le
        (by exact_mod_cast hXmin (i, j))) : ((E i).card : ENNReal) < (X (i, j)).card)
    obtain ⟨g, _, hassign, hpreserve, hdiff⟩ :=
      CapacityPreservingReassignment (V i) (E i) (hES i) (fun v => (f v).2) b hroom'
    refine ⟨g, ?_, ?_, ?_⟩
    · intro v hv
      rw [hassign v hv]
      exact hb v (hES i hv)
    · intro j
      exact (hpreserve j).trans (holdcard j)
    · intro j
      calc
        _ ≤ (2 : ENNReal) * (E i).card := by exact_mod_cast hdiff j
        _ ≤ 2 * ((k : ENNReal) * ε * n) := mul_le_mul_right (hEbound i) 2
        _ = 2 * k * ε * n := by ac_rfl
  choose g hgE hgcard hgdiff using hcorrect
  -- Global fibers are exactly the corrected fibers inside their original clusters.
  let f' : VG → Fin r × Fin k := fun v => (B.hostCluster v, g (B.hostCluster v) v)
  have hnew (i : Fin r) (j : Fin k) :
      (Finset.univ.filter fun v => f' v = (i, j)) = (V i).filter fun v => g i v = j := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, f', V]
    constructor
    · rintro ⟨h, hj⟩
      exact ⟨h, by simpa [h] using hj⟩
    · rintro ⟨h, hj⟩
      exact ⟨h, by simpa [h] using hj⟩
  have hold (i : Fin r) (j : Fin k) :
      (Finset.univ.filter fun v => f v = (i, j)) = (V i).filter fun v => (f v).2 = j := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, V]
    rw [← hf v, Prod.ext_iff]
  refine ⟨f', fun v => rfl, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩
    rw [hnew]
    exact hgcard i j
  · rintro ⟨i, j⟩
    rw [hnew, hold]
    exact hgdiff i j
  · intro v
    simp only [← Finset.filter_filter]
    change (d - 2 * ε) * (X (B.hostCluster v, g (B.hostCluster v) v)).card ≤
      (((X (B.hostCluster v, g (B.hostCluster v) v)).filter fun x => A.allowed x v).card : ENNReal)
    by_cases hv : v ∈ E (B.hostCluster v)
    · exact (mul_le_mul_left (tsub_le_tsub_left htwo d) _).trans
          (hgE (B.hostCluster v) v hv)
    · apply le_of_not_gt
      intro hbad
      apply hv
      exact Finset.mem_biUnion.mpr ⟨g (B.hostCluster v) v, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨by simp [V], hbad⟩⟩
