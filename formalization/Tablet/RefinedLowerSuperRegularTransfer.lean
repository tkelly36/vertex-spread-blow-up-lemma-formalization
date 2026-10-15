import Tablet.CandidacyLowerSuperRegular
import Tablet.InstanceLowerSuperRegular
import Tablet.LowerRegularRestriction

open scoped Classical symmDiff

-- [TABLET NODE: RefinedLowerSuperRegularTransfer]
theorem RefinedLowerSuperRegularTransfer {r k : ℕ} {VH VG : Type*}
    [Fintype VH] [Fintype VG] [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG} {R : SimpleGraph (Fin r)}
    [DecidableRel G.Adj] (B : BlowUpInstance r VH VG H G R)
    (A : CandidacySystem B) (σ : VH → Fin r × Fin k)
    (f f' : VG → Fin r × Fin k) (ε θ d : ENNReal) (n : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n) (hθ : θ < 1)
    (hsmall : (4 * (k : ENNReal) ^ 2 + 2) * ε ≤ θ)
    (hthreshold : 2 * k * ε ≤ θ)
    (hσ : ∀ x, (σ x).1 = B.sourceCluster x)
    (hf : ∀ v, (f v).1 = B.hostCluster v)
    (hf' : ∀ v, (f' v).1 = B.hostCluster v)
    (hcard : ∀ i,
      (Finset.univ.filter fun x => B.sourceCluster x = i).card = n ∧
      (Finset.univ.filter fun v => B.hostCluster v = i).card = n)
    (hsize : ∀ p, (Finset.univ.filter fun x => σ x = p).card = n / k ∨
      (Finset.univ.filter fun x => σ x = p).card = n / k + 1)
    (hcapacity : ∀ p, (Finset.univ.filter fun v => f v = p).card =
      (Finset.univ.filter fun x => σ x = p).card)
    (hcapacity' : ∀ p, (Finset.univ.filter fun v => f' v = p).card =
      (Finset.univ.filter fun x => σ x = p).card)
    (hchange : ∀ p, (((Finset.univ.filter fun v => f' v = p) ∆
        (Finset.univ.filter fun v => f v = p)).card : ENNReal) ≤ 2 * k * ε * n)
    (hsource : ∀ x j, (d - 2 * ε) *
      ((Finset.univ.filter fun v => f v = (B.sourceCluster x, j)).card : ENNReal) ≤
      ((Finset.univ.filter fun v =>
        f v = (B.sourceCluster x, j) ∧ A.allowed x v).card : ENNReal))
    (hhostdegree : ∀ v i j, R.Adj (B.hostCluster v) i →
      (d - 2 * ε) * ((Finset.univ.filter fun w => f w = (i, j)).card : ENNReal) ≤
      ((Finset.univ.filter fun w => f w = (i, j) ∧ G.Adj v w).card : ENNReal))
    (hcandidatedegree : ∀ v, (d - 2 * ε) *
      ((Finset.univ.filter fun x => σ x = f' v).card : ENNReal) ≤
      ((Finset.univ.filter fun x => σ x = f' v ∧ A.allowed x v).card : ENNReal))
    (hhost : InstanceLowerSuperRegular B ε d)
    (hcand : CandidacyLowerSuperRegular B A ε d) :
    (∀ p q, R.Adj p.1 q.1 →
      LowerSuperRegularPair G (Finset.univ.filter fun v => f' v = p)
        (Finset.univ.filter fun v => f' v = q) θ d) ∧
    (∀ p,
      let L : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ x, z = Sum.inl x ∧ σ x = p
      let Q : Finset (VH ⊕ VG) := Finset.univ.filter fun z =>
        ∃ v, z = Sum.inr v ∧ f' v = p
      let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
        ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A.allowed x v
      letI : DecidableRel C.Adj := Classical.decRel _
      LowerSuperRegularPair C L Q θ d) := by
-- BODY
  classical
  have hkpos : 0 < k := hk
  have htwo : (2 : ENNReal) ≤ 4 * (k : ENNReal) ^ 2 + 2 := le_add_left le_rfl
  have h2ε : 2 * ε ≤ θ := (mul_le_mul_left htwo ε).trans hsmall
  have hεθ : ε ≤ θ := by
    calc
      ε ≤ 2 * ε := by
        simpa using mul_le_mul_left (by norm_num : (1 : ENNReal) ≤ 2) ε
      _ ≤ θ := h2ε
  let S (p : Fin r × Fin k) := Finset.univ.filter fun x => σ x = p
  let F (p : Fin r × Fin k) := Finset.univ.filter fun v => f v = p
  let T (p : Fin r × Fin k) := Finset.univ.filter fun v => f' v = p
  have hcap (p) : (F p).card = (S p).card := hcapacity p
  have hcap' (p) : (T p).card = (S p).card := hcapacity' p
  have hnsize (p) : n ≤ 2 * k * (S p).card := by
    have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hkpos).mpr hn
    have hs : n / k ≤ (S p).card := by
      rcases hsize p with h | h <;> dsimp [S] <;> omega
    have hrem := Nat.mod_lt n hkpos
    have hdecomp := Nat.mod_add_div n k
    have hstep : n ≤ k * (n / k + 1) := by nlinarith
    calc
      n ≤ k * (n / k + 1) := hstep
      _ ≤ k * (2 * (n / k)) := Nat.mul_le_mul_left k (by omega)
      _ ≤ k * (2 * (S p).card) := Nat.mul_le_mul_left k (Nat.mul_le_mul_left 2 hs)
      _ = 2 * k * (S p).card := by ring
  have hthresh (p) : ε * n ≤ θ * (S p).card := by
    calc
      ε * n ≤ ε * (2 * k * (S p).card) :=
        mul_le_mul_right (by exact_mod_cast hnsize p) ε
      _ = (2 * k * ε) * (S p).card := by ring
      _ ≤ θ * (S p).card := mul_le_mul_left hthreshold _
  have hloss (p) : 2 * k * ε * n + 2 * ε * (S p).card ≤ θ * (S p).card := by
    calc
      2 * k * ε * n + 2 * ε * (S p).card ≤
          2 * k * ε * (2 * k * (S p).card) + 2 * ε * (S p).card :=
        add_le_add (mul_le_mul_right (by exact_mod_cast hnsize p) _) le_rfl
      _ = ((4 * (k : ENNReal) ^ 2 + 2) * ε) * (S p).card := by ring
      _ ≤ θ * (S p).card := mul_le_mul_left hsmall _
  -- Additive inequalities avoid cancellation or finiteness assumptions on d.
  have htransfer (p) (P : VG → Prop) [DecidablePred P]
      (hdegree : (d - 2 * ε) * (F p).card ≤ ((F p |>.filter P).card : ENNReal)) :
      (d - θ) * (T p).card ≤ ((T p |>.filter P).card : ENNReal) := by
    have hsub : (F p).filter P ⊆ (T p).filter P ∪ (T p ∆ F p) := by
      intro v hv
      obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
      by_cases hvT : v ∈ T p
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvT, hvP⟩)
      · exact Finset.mem_union_right _ (by simp [Finset.mem_symmDiff, hvT, hvF])
    have hcount : (((F p).filter P).card : ENNReal) ≤
        ((T p).filter P).card + 2 * k * ε * n := by
      calc
        (((F p).filter P).card : ENNReal) ≤ ((T p).filter P ∪ (T p ∆ F p)).card := by
          exact_mod_cast Finset.card_le_card hsub
        _ ≤ (((T p).filter P).card : ENNReal) + (T p ∆ F p).card := by
          exact_mod_cast Finset.card_union_le ((T p).filter P) (T p ∆ F p)
        _ ≤ _ := add_le_add le_rfl (hchange p)
    rw [hcap, ENNReal.sub_mul (fun _ _ => ENNReal.natCast_ne_top _)] at hdegree
    rw [hcap', ENNReal.sub_mul (fun _ _ => ENNReal.natCast_ne_top _)]
    apply tsub_le_iff_right.mpr
    calc
      d * (S p).card ≤ (((F p).filter P).card : ENNReal) + 2 * ε * (S p).card :=
        tsub_le_iff_right.mp hdegree
      _ ≤ (((T p).filter P).card : ENNReal) + 2 * k * ε * n + 2 * ε * (S p).card :=
        add_le_add hcount le_rfl
      _ ≤ (((T p).filter P).card : ENNReal) + θ * (S p).card := by
        rw [add_assoc]
        exact add_le_add le_rfl (hloss p)
  have hTsub (p) : T p ⊆ Finset.univ.filter (fun v => B.hostCluster v = p.1) := by
    intro v hv
    have hvp : f' v = p := (Finset.mem_filter.mp hv).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hf' v).symm.trans (congrArg Prod.fst hvp)
  constructor
  · intro p q hpq
    refine ⟨LowerRegularRestriction G _ _ (T p) (T q) ε θ d
      (hTsub p) (hTsub q) hεθ ?_ ?_ (hhost hpq).1, ?_, ?_⟩
    · simpa only [(hcard p.1).2, hcap'] using hthresh p
    · simpa only [(hcard q.1).2, hcap'] using hthresh q
    · intro v hv
      have hvp : B.hostCluster v = p.1 := (Finset.mem_filter.mp (hTsub p hv)).2
      have hd := hhostdegree v q.1 q.2 (hvp.symm ▸ hpq)
      apply htransfer q (fun w => G.Adj v w)
      simpa only [F, Finset.filter_filter, Prod.eta] using hd
    · intro w hw
      have hwq : B.hostCluster w = q.1 := (Finset.mem_filter.mp (hTsub q hw)).2
      have hd := hhostdegree w p.1 p.2 (hwq.symm ▸ hpq.symm)
      have ht := htransfer p (fun v => G.Adj w v) (by
        simpa only [F, Finset.filter_filter, Prod.eta] using hd)
      simpa only [T, G.adj_comm] using ht
  · intro p
    let C : SimpleGraph (VH ⊕ VG) := SimpleGraph.fromRel fun a b =>
      ∃ x v, a = Sum.inl x ∧ b = Sum.inr v ∧ A.allowed x v
    letI : DecidableRel C.Adj := Classical.decRel _
    let left (U : Finset VH) : Finset (VH ⊕ VG) := U.map Function.Embedding.inl
    let right (W : Finset VG) : Finset (VH ⊕ VG) := W.map Function.Embedding.inr
    have hleft (g : VH → Fin r × Fin k) :
        left (Finset.univ.filter fun x => g x = p) =
          Finset.univ.filter (fun z : VH ⊕ VG => ∃ x, z = Sum.inl x ∧ g x = p) := by
      ext z
      cases z <;> simp [left]
    have hright (g : VG → Fin r × Fin k) :
        right (Finset.univ.filter fun v => g v = p) =
          Finset.univ.filter (fun z : VH ⊕ VG => ∃ v, z = Sum.inr v ∧ g v = p) := by
      ext z
      cases z <;> simp [right]
    change LowerSuperRegularPair C _ _ θ d
    rw [← hleft σ, ← hright f']
    change LowerSuperRegularPair C (left (S p)) (right (T p)) θ d
    let U := Finset.univ.filter fun x => B.sourceCluster x = p.1
    let W := Finset.univ.filter fun v => B.hostCluster v = p.1
    have hpair : LowerSuperRegularPair C (left U) (right W) ε d := by
      have hU : left U = Finset.univ.filter (fun z : VH ⊕ VG =>
          ∃ x, z = Sum.inl x ∧ B.sourceCluster x = p.1) := by
        ext z
        cases z <;> simp [left, U]
      have hW : right W = Finset.univ.filter (fun z : VH ⊕ VG =>
          ∃ v, z = Sum.inr v ∧ B.hostCluster v = p.1) := by
        ext z
        cases z <;> simp [right, W]
      rw [hU, hW]
      exact hcand p.1
    have hSsub : S p ⊆ U := by
      intro x hx
      have hxp : σ x = p := (Finset.mem_filter.mp hx).2
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hσ x).symm.trans (congrArg Prod.fst hxp)
    have hLsub : left (S p) ⊆ left U := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_map.mpr ⟨x, hSsub hx, rfl⟩
    have hQsub : right (T p) ⊆ right W := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_map.mpr ⟨v, hTsub p hv, rfl⟩
    have hreg : LowerRegularPair C (left (S p)) (right (T p)) θ d := by
      apply LowerRegularRestriction C (left U) (right W) _ _ ε θ d hLsub hQsub hεθ
      · simpa only [left, Finset.card_map, U, (hcard p.1).1] using hthresh p
      · simpa only [right, Finset.card_map, W, (hcard p.1).2, hcap'] using hthresh p
      · exact hpair.1
    have hadj (x : VH) (v : VG) : C.Adj (Sum.inl x) (Sum.inr v) ↔ A.allowed x v := by
      simp [C, SimpleGraph.fromRel_adj]
    refine ⟨hreg, ?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
      have hxp : σ x = p := (Finset.mem_filter.mp hx).2
      have hxi : B.sourceCluster x = p.1 := (hσ x).symm.trans (congrArg Prod.fst hxp)
      simp only [Function.Embedding.inl_apply]
      simp only [right, Finset.filter_map, Finset.card_map, Function.comp_def,
        Function.Embedding.inr_apply, hadj]
      apply htransfer p (fun v => A.allowed x v)
      have hd := hsource x p.2
      simpa only [hxi, Prod.eta, F, Finset.filter_filter] using hd
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
      have hvp : f' v = p := (Finset.mem_filter.mp hv).2
      simp only [Function.Embedding.inr_apply]
      simp only [left, Finset.filter_map, Finset.card_map, Function.comp_def,
        Function.Embedding.inl_apply, hadj]
      have hd := hcandidatedegree v
      have hd' : (d - 2 * ε) * (S p).card ≤
          (((S p).filter fun x => A.allowed x v).card : ENNReal) := by
        simpa only [hvp, S, Finset.filter_filter] using hd
      exact (mul_le_mul_left (tsub_le_tsub_left h2ε d) _).trans hd'
