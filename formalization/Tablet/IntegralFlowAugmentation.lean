import Tablet.SimpleResidualPath
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

open scoped BigOperators

-- [TABLET NODE: IntegralFlowAugmentation]
theorem IntegralFlowAugmentation {V : Type*} [Fintype V] [DecidableEq V]
    {N : FiniteCapacityNetwork V} (f : FiniteIntegralFlow N)
    (p : SimpleResidualPath f) :
    ∃ (δ : ℤ) (g : FiniteIntegralFlow N),
      0 < δ ∧
      (∀ i : Fin p.length,
        δ ≤ (N.capacity (p.vertex i.castSucc) (p.vertex i.succ) : ℤ) -
          f.amount (p.vertex i.castSucc) (p.vertex i.succ)) ∧
      (∀ v w, g.amount v w = f.amount v w + δ *
        (((Finset.univ.filter fun i : Fin p.length =>
          p.vertex i.castSucc = v ∧ p.vertex i.succ = w).card : ℤ) -
         ((Finset.univ.filter fun i : Fin p.length =>
          p.vertex i.castSucc = w ∧ p.vertex i.succ = v).card : ℤ))) ∧
      (∑ w, g.amount N.source w) = (∑ w, f.amount N.source w) + δ := by
-- BODY
  classical
  let r (i : Fin p.length) : ℤ :=
    (N.capacity (p.vertex i.castSucc) (p.vertex i.succ) : ℤ) -
      f.amount (p.vertex i.castSucc) (p.vertex i.succ)
  let S := Finset.univ.image r
  have hS : S.Nonempty := by
    exact ⟨r ⟨0, p.positive⟩, Finset.mem_image.mpr ⟨⟨0, p.positive⟩, by simp, rfl⟩⟩
  let δ := S.min' hS
  have hδ : 0 < δ := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    have hr := p.residual i
    dsimp [r] at hi
    dsimp [δ]
    rw [← hi]
    exact sub_pos.mpr hr
  have hδr (i : Fin p.length) : δ ≤ r i :=
    Finset.min'_le S (r i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  let C (v w : V) : ℤ :=
    ((Finset.univ.filter fun i : Fin p.length =>
      p.vertex i.castSucc = v ∧ p.vertex i.succ = w).card : ℤ)
  have hCnonneg (v w : V) : 0 ≤ C v w := by
    dsimp [C]
    positivity
  have hCle (v w : V) : C v w ≤ 1 := by
    have hc : (Finset.univ.filter fun i : Fin p.length =>
        p.vertex i.castSucc = v ∧ p.vertex i.succ = w).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      have he : i.castSucc = j.castSucc := p.injective
        ((Finset.mem_filter.mp hi).2.1.trans (Finset.mem_filter.mp hj).2.1.symm)
      exact Fin.castSucc_injective _ he
    dsimp [C]
    exact_mod_cast hc
  let a (v w : V) := f.amount v w + δ * (C v w - C w v)
  have habound (v w : V) : a v w ≤ (N.capacity v w : ℤ) := by
    by_cases hc : C v w = 0
    · dsimp [a]
      have hb := f.bound v w
      have hn := hCnonneg w v
      nlinarith
    · have hpos : 0 < (Finset.univ.filter fun i : Fin p.length =>
          p.vertex i.castSucc = v ∧ p.vertex i.succ = w).card := by
        by_contra hn
        have hz : (Finset.univ.filter fun i : Fin p.length =>
            p.vertex i.castSucc = v ∧ p.vertex i.succ = w).card = 0 := by omega
        exact hc (by simp [C, hz])
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      obtain ⟨hv, hw⟩ := (Finset.mem_filter.mp hi).2
      have hr := hδr i
      dsimp [r] at hr
      rw [hv, hw] at hr
      have hf := hCle v w
      have hb := hCnonneg w v
      dsimp [a]
      nlinarith
  have hCsum (v w : V) : C v w =
      ∑ i : Fin p.length, if p.vertex i.castSucc = v ∧ p.vertex i.succ = w
        then (1 : ℤ) else 0 := by
    simp [C, Finset.sum_boole]
  have hdepart (v : V) : (∑ w, C v w) =
      ∑ i : Fin p.length, if p.vertex i.castSucc = v then (1 : ℤ) else 0 := by
    simp_rw [hCsum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : p.vertex i.castSucc = v <;> simp [h]
  have harrive (v : V) : (∑ w, C w v) =
      ∑ i : Fin p.length, if p.vertex i.succ = v then (1 : ℤ) else 0 := by
    simp_rw [hCsum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : p.vertex i.succ = v <;> simp [h]
  have htel (b : Fin (p.length + 1) → ℤ) :
      (∑ i : Fin p.length, b i.castSucc) - (∑ i : Fin p.length, b i.succ) =
        b 0 - b (Fin.last p.length) := by
    have h₁ := Fin.sum_univ_castSucc b
    have h₂ := Fin.sum_univ_succ b
    linarith
  have harow (v : V) : (∑ w, a v w) = (∑ w, f.amount v w) +
      δ * ((if N.source = v then (1 : ℤ) else 0) -
        (if N.sink = v then (1 : ℤ) else 0)) := by
    simp only [a, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hdepart, harrive]
    rw [htel (fun j => if p.vertex j = v then (1 : ℤ) else 0)]
    rw [p.start, p.finish]
  let g : FiniteIntegralFlow N := {
    amount := a
    skew := by
      intro v w
      dsimp [a]
      rw [f.skew v w]
      ring
    bound := habound
    conserve := by
      intro v hs ht
      rw [harow, f.conserve v hs ht]
      simp [Ne.symm hs, Ne.symm ht] }
  refine ⟨δ, g, hδ, hδr, ?_, ?_⟩
  · intro v w
    rfl
  · change (∑ w, a N.source w) = _
    rw [harow]
    simp [Ne.symm N.terminals_distinct]
