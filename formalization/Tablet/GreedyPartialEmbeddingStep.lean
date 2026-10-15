import Tablet.GreedyPartialEmbedding
import Tablet.InstanceLowerRegular
import Tablet.LowerRegularBadRows

-- [TABLET NODE: GreedyPartialEmbeddingStep]
theorem GreedyPartialEmbeddingStep (Δ : ℕ) (d ε a : ENNReal) (n : ℕ)
    (hn : 0 < n) (ha : 0 < a)
    (hpower : ∀ k : ℕ, k ≤ Δ → a ≤ d * (d - ε) ^ k)
    (hthreshold : ε * (1 + ε) < a)
    (hloss : (Δ + 1 : ENNReal) * ε * (1 + ε) ≤ a / 2)
    {r : ℕ} {VH VG : Type*} [Fintype VH] [Fintype VG]
    [DecidableEq VH] [DecidableEq VG]
    {H : SimpleGraph VH} {G : SimpleGraph VG}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    {R : SimpleGraph (Fin r)}
    (B : BlowUpInstance r VH VG H G R) (A : CandidacySystem B)
    (hreg : InstanceLowerRegular B ε d) (hdeg : H.maxDegree ≤ Δ)
    (hsmall : ∀ i, (Fintype.card {x : VH // B.sourceCluster x = i} : ENNReal) ≤
      ε * Fintype.card {v : VG // B.hostCluster v = i})
    (hhost : ∀ i, (Fintype.card {v : VG // B.hostCluster v = i} : ENNReal) ≤
      (1 + ε) * n)
    (S : Finset VH) (f : GreedyPartialEmbedding B A d ε n S)
    (z : VH) (hz : z ∉ S) :
    ∃ L : Finset VG, L.Nonempty ∧ a / 2 * n ≤ (L.card : ENNReal) ∧
      ∀ v ∈ L, ∃ g : GreedyPartialEmbedding B A d ε n (insert z S),
        g.toFun = Function.update f.toFun z v := by
-- BODY
  classical
  let V (i : Fin r) := Finset.univ.filter fun v => B.hostCluster v = i
  let W (x : VH) := RawCandidates B A S f.toFun x
  have memraw (x : VH) (v : VG) : v ∈ W x ↔
      A.allowed x v ∧ ∀ y ∈ S, H.Adj x y → G.Adj v (f.toFun y) := by
    simp [W, RawCandidates]
  have hVcard (i : Fin r) : (V i).card =
      Fintype.card {v : VG // B.hostCluster v = i} := by
    simp [V, Fintype.card_subtype]
  have hWsub (x : VH) : W x ⊆ V (B.sourceCluster x) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (A.cluster_respecting ((memraw x v).mp hv).1).symm⟩
  have hk (x : VH) : (S.filter fun y => H.Adj x y).card ≤ Δ := by
    apply le_trans _ ((H.degree_le_maxDegree x).trans hdeg)
    change (S.filter fun y => H.Adj x y).card ≤ (H.neighborFinset x).card
    apply Finset.card_le_card
    intro y hy
    exact (H.mem_neighborFinset x y).mpr (Finset.mem_filter.mp hy).2
  have hraw (x : VH) (hx : x ∉ S) : a * n ≤ ((W x).card : ENNReal) := by
    exact (mul_le_mul_left (hpower _ (hk x)) (n : ENNReal)).trans (f.raw_bound x hx)
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have han : a * n ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hraw z hz)
  have hatop : a ≠ ⊤ := (ENNReal.lt_top_of_mul_ne_top_left han hn0).ne
  let U := (H.neighborFinset z) \ S
  let E (w : VH) := (V (B.sourceCluster z)).filter fun v =>
    (((W w).filter fun u => G.Adj v u).card : ENNReal) < (d - ε) * (W w).card
  have hUcard : U.card ≤ Δ :=
    (Finset.card_le_card (Finset.sdiff_subset : U ⊆ H.neighborFinset z)).trans
      ((H.degree_le_maxDegree z).trans hdeg)
  have hEcard (w : VH) (hw : w ∈ U) :
      ((E w).card : ENNReal) ≤ ε * (V (B.sourceCluster z)).card := by
    obtain ⟨hzw, hwS⟩ := Finset.mem_sdiff.mp hw
    have hzw' := (H.mem_neighborFinset z w).mp hzw
    apply LowerRegularBadRows G (V (B.sourceCluster z))
      (V (B.sourceCluster w)) (W w) ε d
      (hreg (B.reduced_support hzw')) (hWsub w)
    calc
      ε * (V (B.sourceCluster w)).card ≤ ε * ((1 + ε) * n) := by
        rw [hVcard]
        exact mul_le_mul_right (hhost _) ε
      _ = (ε * (1 + ε)) * n := (mul_assoc _ _ _).symm
      _ < a * n := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_right hn0 (by simp) hthreshold
      _ ≤ ((W w).card : ENNReal) := hraw w hwS
  let O := (S.filter fun y => B.sourceCluster y = B.sourceCluster z).image f.toFun
  have hOcard : O.card ≤ Fintype.card {y : VH // B.sourceCluster y = B.sourceCluster z} := by
    apply (Finset.card_image_le).trans
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hO : (O.card : ENNReal) ≤ ε * (V (B.sourceCluster z)).card := by
    rw [hVcard]
    have hOcard' : (O.card : ENNReal) ≤ Fintype.card {y : VH // B.sourceCluster y = B.sourceCluster z} :=
      by exact_mod_cast hOcard
    exact hOcard'.trans (hsmall _)
  let F := O ∪ U.biUnion E
  have hF : (F.card : ENNReal) ≤ a / 2 * n := by
    calc
      (F.card : ENNReal) ≤ (O.card : ENNReal) + (U.biUnion E).card := by
        exact_mod_cast (Finset.card_union_le O (U.biUnion E))
      _ ≤ ε * (V (B.sourceCluster z)).card + ∑ w ∈ U, ((E w).card : ENNReal) := by
        apply add_le_add hO
        exact_mod_cast (Finset.card_biUnion_le (s := U) (t := E))
      _ ≤ ε * (V (B.sourceCluster z)).card +
          ∑ _w ∈ U, ε * (V (B.sourceCluster z)).card := by
        exact add_le_add le_rfl (Finset.sum_le_sum hEcard)
      _ = ((U.card : ENNReal) + 1) * ε * (V (B.sourceCluster z)).card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        simp only [add_mul, one_mul]
        simp only [mul_assoc, mul_comm, mul_left_comm, add_comm]
      _ ≤ (Δ + 1 : ENNReal) * ε * (V (B.sourceCluster z)).card := by
        gcongr
      _ ≤ (Δ + 1 : ENNReal) * ε * ((1 + ε) * n) := by
        rw [hVcard]
        exact mul_le_mul_right (hhost _) _
      _ = ((Δ + 1 : ENNReal) * ε * (1 + ε)) * n := (mul_assoc _ _ _).symm
      _ ≤ a / 2 * n := mul_le_mul_left hloss _
  let L := W z \ F
  have hL : a / 2 * n ≤ (L.card : ENNReal) := by
    have hcount : ((W z).card : ENNReal) ≤ (L.card : ENNReal) + F.card := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := W z) (t := F))
    have hhalftop : a / 2 * n ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.div_ne_top hatop (by norm_num)) (by simp)
    apply ENNReal.le_of_add_le_add_right hhalftop
    calc
      a / 2 * n + a / 2 * n = a * n := by rw [← add_mul, ENNReal.add_halves]
      _ ≤ ((W z).card : ENNReal) := hraw z hz
      _ ≤ (L.card : ENNReal) + F.card := hcount
      _ ≤ (L.card : ENNReal) + a / 2 * n := add_le_add le_rfl hF
  have hLpos : (0 : ENNReal) < L.card :=
    (ENNReal.mul_pos (ENNReal.half_pos ha.ne').ne' hn0).trans_le hL
  refine ⟨L, Finset.card_pos.mp (by exact_mod_cast hLpos), hL, ?_⟩
  intro v hv
  obtain ⟨hvr, hvF⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hvA, hvadj⟩ := (memraw z v).mp hvr
  have hvO : v ∉ O := fun h => hvF (Finset.mem_union_left _ h)
  have hvE (w : VH) (hw : w ∈ U) : v ∉ E w := by
    intro h
    exact hvF (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, h⟩))
  have hvnew : ∀ y ∈ S, f.toFun y ≠ v := by
    intro y hy heq
    have hycluster : B.sourceCluster y = B.sourceCluster z := by
      calc
        B.sourceCluster y = B.hostCluster (f.toFun y) :=
          A.cluster_respecting (f.compatible y hy)
        _ = B.hostCluster v := congrArg B.hostCluster heq
        _ = B.sourceCluster z := (A.cluster_respecting hvA).symm
    exact hvO (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hycluster⟩, heq⟩)
  have hupdate (y : VH) (hy : y ∈ S) : Function.update f.toFun z v y = f.toFun y := by
    exact Function.update_of_ne (ne_of_mem_of_not_mem hy hz) v f.toFun
  let g : GreedyPartialEmbedding B A d ε n (insert z S) :=
    { toFun := Function.update f.toFun z v
      injOn := by
        intro x hx y hy heq
        by_cases hxz : x = z
        · subst x
          by_cases hyz : y = z
          · exact hyz.symm
          · have hyS := (Finset.mem_insert.mp hy).resolve_left hyz
            have h : v = f.toFun y := by simpa only [Function.update_self, hupdate y hyS] using heq
            exact (hvnew y hyS h.symm).elim
        · have hxS := (Finset.mem_insert.mp hx).resolve_left hxz
          by_cases hyz : y = z
          · subst y
            have h : f.toFun x = v := by simpa only [Function.update_self, hupdate x hxS] using heq
            exact (hvnew x hxS h).elim
          · have hyS := (Finset.mem_insert.mp hy).resolve_left hyz
            exact f.injOn hxS hyS (by simpa only [hupdate x hxS, hupdate y hyS] using heq)
      map_adj := by
        intro x y hx hy hxy
        by_cases hxz : x = z
        · subst x
          have hyz : y ≠ z := hxy.ne.symm
          have hyS := (Finset.mem_insert.mp hy).resolve_left hyz
          simpa only [Function.update_self, hupdate y hyS] using hvadj y hyS hxy
        · have hxS := (Finset.mem_insert.mp hx).resolve_left hxz
          by_cases hyz : y = z
          · subst y
            simpa only [Function.update_self, hupdate x hxS] using (hvadj x hxS hxy.symm).symm
          · have hyS := (Finset.mem_insert.mp hy).resolve_left hyz
            simpa only [hupdate x hxS, hupdate y hyS] using f.map_adj hxS hyS hxy
      compatible := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simpa only [Function.update_self] using hvA
        · simpa only [hupdate x hx] using f.compatible x hx
      raw_bound := by
        intro x hx
        have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
        by_cases hxz : H.Adj x z
        · have hxU : x ∈ U := Finset.mem_sdiff.mpr
            ⟨(H.mem_neighborFinset z x).mpr hxz.symm, hxS⟩
          have hgood : (d - ε) * (W x).card ≤
              (((W x).filter fun u => G.Adj v u).card : ENNReal) := by
            apply le_of_not_gt
            intro hbad
            exact hvE x hxU (Finset.mem_filter.mpr ⟨hWsub z hvr, hbad⟩)
          have hrawupdate : RawCandidates B A (insert z S) (Function.update f.toFun z v) x =
              (W x).filter fun u => G.Adj v u := by
            ext u
            simp only [RawCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨huA, huadj⟩
              refine ⟨(memraw x u).mpr ⟨huA, ?_⟩, ?_⟩
              · intro y hy hxy
                simpa only [hupdate y hy] using huadj y (Finset.mem_insert_of_mem hy) hxy
              · simpa only [Function.update_self] using
                  (huadj z (Finset.mem_insert_self _ _) hxz).symm
            · rintro ⟨hur, huv⟩
              obtain ⟨huA, huadj⟩ := (memraw x u).mp hur
              refine ⟨huA, ?_⟩
              intro y hy hxy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · simpa only [Function.update_self] using huv.symm
              · simpa only [hupdate y hy] using huadj y hy hxy
          have hcount : ((insert z S).filter fun y => H.Adj x y).card =
              (S.filter fun y => H.Adj x y).card + 1 := by
            rw [Finset.filter_insert, if_pos hxz, Finset.card_insert_of_notMem]
            exact fun h => hz (Finset.mem_filter.mp h).1
          rw [hrawupdate, hcount, pow_succ]
          calc
            d * ((d - ε) ^ (S.filter fun y => H.Adj x y).card * (d - ε)) * n =
                (d - ε) * (d * (d - ε) ^ (S.filter fun y => H.Adj x y).card * n) := by ac_rfl
            _ ≤ (d - ε) * (W x).card := mul_le_mul_right (f.raw_bound x hxS) _
            _ ≤ _ := hgood
        · have hrawupdate : RawCandidates B A (insert z S) (Function.update f.toFun z v) x = W x := by
            ext u
            simp only [RawCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨huA, huadj⟩
              refine (memraw x u).mpr ⟨huA, ?_⟩
              intro y hy hxy
              simpa only [hupdate y hy] using huadj y (Finset.mem_insert_of_mem hy) hxy
            · intro hur
              obtain ⟨huA, huadj⟩ := (memraw x u).mp hur
              refine ⟨huA, ?_⟩
              intro y hy hxy
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact (hxz hxy).elim
              · simpa only [hupdate y hy] using huadj y hy hxy
          have hcount : (insert z S).filter (fun y => H.Adj x y) =
              S.filter (fun y => H.Adj x y) := by
            rw [Finset.filter_insert, if_neg hxz]
          rw [hrawupdate, hcount]
          exact f.raw_bound x hxS }
  exact ⟨g, rfl⟩
