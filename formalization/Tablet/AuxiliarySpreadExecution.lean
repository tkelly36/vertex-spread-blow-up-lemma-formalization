import Tablet.EqualSizeParameterTable
import Tablet.VariableSizeInductionIteration
import Tablet.EqualSizeTerminalConversion
import Tablet.SuperRegularErrorMonotone

-- [TABLET NODE: AuxiliarySpreadExecution]
theorem AuxiliarySpreadExecution :
    ∀ (d : ENNReal) (D : ℕ), 0 < d → d ≤ 1 →
      ∃ (ε C : ENNReal) (N : ℕ),
        0 < ε ∧ ε < 1 ∧ 1 ≤ C ∧ C < ⊤ ∧ 1 ≤ N ∧
        ∀ (r n : ℕ), N ≤ n →
        ∀ {VH VG : Type*} [Fintype VH] [Fintype VG]
          [DecidableEq VH] [DecidableEq VG]
          {H : SimpleGraph VH} {G : SimpleGraph VG} [DecidableRel G.Adj]
          {R : SimpleGraph (Fin r)} [DecidableRel R.Adj]
          (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B),
          (∀ j : Fin r,
            ((Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n ∨
             (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card = n + 1) ∧
            (Finset.univ.filter fun x : VH => B.sourceCluster x = j).card =
              (Finset.univ.filter fun v : VG => B.hostCluster v = j).card) →
          R.maxDegree ≤ D →
          InstanceSuperRegular B ε d → CandidacySuperRegular B A ε d →
          (∀ ⦃i j : Fin r⦄, R.Adj i j → SaturatingSourcePair B i j) →
          ∃ μ : PMF {φ : SimpleGraph.Copy H G // CompatibleEmbedding B A φ},
            VertexSpreadOn (μ.map fun φ => fun x => φ.1 x) (C / n) Set.univ := by
-- BODY
  classical
  intro d D hd hd1
  obtain ⟨p, rho, e, omega, theta, zeta, hatZeta, cert, a, M, C, N₀,
    hp0, hdens, hrec, hround, ha, ha1, hM, hMC, hthreshold, horder⟩ :=
    EqualSizeParameterTable.{0, 0, 0, 0, 0} d D hd hd1
  have hzero : 0 < D ^ 2 + 1 := Nat.zero_lt_succ _
  have he0 := (hround 0 hzero).1
  have he01 : e 0 ≤ 1 := (hround 0 hzero).2.2.2.2.2.2.1.trans
    (hround 0 hzero).2.2.2.2.2.2.2.1
  have hC : 1 ≤ C := by
    calc
      1 ≤ M := hM
      _ ≤ 2 * M := by
        simpa only [one_mul] using mul_le_mul_right' (by norm_num : (1 : ENNReal) ≤ 2) M
      _ ≤ C := hMC
  have hCtop : C < ⊤ := by
    have hk : ((max N₀ 1 : ℕ) : ENNReal) ≠ 0 := by simp
    have hbound := (ENNReal.div_le_iff hk (by simp)).mp
      (horder (max N₀ 1) (le_max_left _ _)).1
    have hbound' : C ≤ ((max N₀ 1 : ℕ) : ENNReal) := by
      simpa only [one_mul] using hbound
    exact hbound'.trans_lt (by simp)
  have hMinv : M ≤ C / 2 :=
    (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      (by simpa only [mul_comm] using hMC)
  have hsmall (s : Fin (D ^ 2 + 1)) : ∃ k : ℕ, (k : ENNReal)⁻¹ < e s :=
    ENNReal.exists_inv_nat_lt (hround s s.isLt).1.ne'
  choose K hK using hsmall
  let N := max N₀ (max 1 (Finset.univ.sup K))
  have hN : 1 ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨e 0 / 2, C, N, ENNReal.half_pos he0.ne', ?_, hC, hCtop, hN, ?_⟩
  · exact (ENNReal.half_lt_self he0.ne'
      (ne_top_of_le_ne_top (by simp) he01)).trans_le he01
  intro r n hn VH VG _ _ _ _ H G _ R _ B A hsizes hR hG hA hsat
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hinv (s : ℕ) (hs : s < D ^ 2 + 1) : 1 / (n : ENNReal) ≤ e s := by
    have hKn : K ⟨s, hs⟩ ≤ n :=
      (Finset.le_sup (f := K) (Finset.mem_univ ⟨s, hs⟩)).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
    have hi : (n : ENNReal)⁻¹ ≤ (K ⟨s, hs⟩ : ENNReal)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast hKn)
    simpa only [one_div] using hi.trans (hK ⟨s, hs⟩).le
  have hstatic : ∀ s, s < D ^ 2 + 1 →
      e s ≤ e (s + 1) ∧ e (s + 1) ≤ 1 ∧
      2 * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + D * (zeta s) ^ (2 : ℝ)⁻¹ ≤ theta s ∧
      zeta s + 2 * D * zeta s ≤ theta s ∧
      (∀ x, x ≤ D → 0 < theta s ∧ 4 * theta s < rho x) ∧
      (∀ x, x ≤ D → 2 * zeta s < rho x ∧ 2 * zeta s < 1 - rho x) ∧
      2 * zeta s < d / 2 ∧ 2 * zeta s < 1 - d / 2 ∧
      (∀ x, x < D → p (x + 1) + e s + 1 / (n : ENNReal) ≤ p x) ∧
      omega (s + 1) < e (s + 1) := by
    intro s hs
    obtain ⟨_, _, _, ht, _, ho, hemono, he1, hroot, hsum, hlinear,
      hsmall, hhalf, hcomp, hgap⟩ := hround s hs
    refine ⟨hemono, he1, hroot, hsum, hlinear,
      (fun x hx => ⟨ht, (hsmall x hx).1⟩),
      (fun x hx => (hsmall x hx).2), hhalf, hcomp, ?_, ho⟩
    intro x hx
    have hnext : p (x + 1) ≤ p x := (tsub_pos_iff_lt.mp
      ((zero_le (2 * e s)).trans_lt (hgap x hx))).le
    have hgap' : p (x + 1) + 2 * e s ≤ p x :=
      (ENNReal.le_sub_iff_add_le_left
        (ne_top_of_le_ne_top (by simp) (hdens (x + 1) (by omega)).2.1) hnext).mp
        (hgap x hx).le
    calc
      _ ≤ p (x + 1) + e s + e s := add_le_add le_rfl (hinv s hs)
      _ = p (x + 1) + 2 * e s := by rw [two_mul, add_assoc]
      _ ≤ p x := hgap'
  have hreserve : ∀ s, s < D ^ 2 + 1 →
      (n : ENNReal)⁻¹ ≤ hatZeta s ∧ hatZeta s < zeta s ∧
      hatZeta s + 2 / (n : ENNReal) ≤ zeta s ∧
      hatZeta s + 1 / (zeta s * (n : ENNReal)) ≤ zeta s ∧
      omega (s + 1) + 2 / (n : ENNReal) ≤ e (s + 1) ∧
      omega (s + 1) + 1 / (e (s + 1) * (n : ENNReal)) ≤ e (s + 1) := by
    intro s hs
    obtain ⟨hi, _, hp, hn, ho, hnorm⟩ := (horder n hn₀).2.2 s hs
    exact ⟨hi, (hround s hs).2.2.1, hp, hn, ho, hnorm⟩
  have hG' : InstanceSuperRegular B (e 0) d := by
    intro i j hij
    exact SuperRegularErrorMonotone _ _ _ _ _ _ ENNReal.half_le_self (hG hij)
  have hA' : CandidacySuperRegular B A (e 0) d := by
    intro i
    exact @SuperRegularErrorMonotone _ _ _ (Classical.decRel _) _ _ _ _ _
      ENNReal.half_le_self (hA i)
  obtain ⟨colour, μ, hμ⟩ := VariableSizeInductionIteration d D p rho e omega theta
    zeta hatZeta cert a C n hp0 hrec ha ha1 (horder n hn₀).1 (horder n hn₀).2.1
      hstatic (by
        intro s hs
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨_, hMbound, hw, hh, hm, he⟩ := (hthreshold s hs).1 x hx
          exact ⟨hw.trans hn₀, hh.trans hn₀, hm.trans hn₀, he.trans hn₀,
            hMbound.trans hMinv⟩
        · intro x y hx hy
          obtain ⟨haconst, hthresh⟩ := (hthreshold s hs).2 x y hx hy
          exact ⟨hthresh.trans hn₀, haconst⟩) hreserve B A hsizes hR hG' hA' hsat
  obtain ⟨F, _, hspread⟩ := EqualSizeTerminalConversion B A Finset.univ μ (C / n)
    rfl hμ.2.2.2.2.2.1
  exact ⟨μ.map F, hspread⟩
