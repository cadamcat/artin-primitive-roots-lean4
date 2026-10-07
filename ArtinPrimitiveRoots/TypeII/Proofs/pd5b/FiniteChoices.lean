import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.Characters

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- A finite choice sum with a fixed prescribed value at each constrained coordinate. -/
theorem pd5b_forced_coordinate_sum_le {n : ℕ}
    (P : Fin n → Finset ℕ) (ν : Fin n → ℕ → ℝ)
    (R : Finset (Fin n)) (pick : Fin n → ℕ) (Δ : ℝ)
    (hΔ : 0 ≤ Δ)
    (hν : ∀ k p, p ∈ P k → 0 ≤ ν k p)
    (hatom : ∀ k ∈ R, ∀ p ∈ P k, ν k p ≤ Δ) :
    (∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
      if ∀ k ∈ R, (b k).1 = pick k then
        ∏ k : Fin n, ν k (b k).1 else 0) ≤
      ∏ k : Fin n, if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
  classical
  let locWeight (k : Fin n) (p : {p : ℕ // p ∈ P k}) : ℝ :=
    if k ∈ R then if p.1 = pick k then ν k p.1 else 0 else ν k p.1
  have hterm (b : (k : Fin n) → {p : ℕ // p ∈ P k}) :
      (if ∀ k ∈ R, (b k).1 = pick k then
        ∏ k : Fin n, ν k (b k).1 else 0) =
      ∏ k : Fin n, locWeight k (b k) := by
    by_cases hall : ∀ k ∈ R, (b k).1 = pick k
    · have hprod : (∏ k : Fin n, locWeight k (b k)) =
          ∏ k : Fin n, ν k (b k).1 := by
        apply Finset.prod_congr rfl
        intro k hk
        by_cases hkR : k ∈ R
        · simp [locWeight, hkR, hall k hkR]
        · simp [locWeight, hkR]
      rw [if_pos hall]
      exact hprod.symm
    · have hex : ∃ k ∈ R, (b k).1 ≠ pick k := by
        push_neg at hall
        exact hall
      obtain ⟨k, hkR, hneq⟩ := hex
      have hzero : (∏ k : Fin n, locWeight k (b k)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        simp [locWeight, hkR, hneq]
      rw [if_neg hall]
      exact hzero.symm
  have hsumFactor :
      (∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
        ∏ k : Fin n, locWeight k (b k)) =
        ∏ k : Fin n, ∑ p : {p : ℕ // p ∈ P k}, locWeight k p := by
    exact (Fintype.prod_sum (fun k p => locWeight k p)).symm
  have hcoord (k : Fin n) :
      (∑ p : {p : ℕ // p ∈ P k}, locWeight k p) ≤
        if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
    by_cases hkR : k ∈ R
    · rw [if_pos hkR]
      dsimp [locWeight]
      simp only [if_pos hkR]
      change (∑ p ∈ (P k).attach,
        if p.1 = pick k then ν k p.1 else 0) ≤ Δ
      by_cases hpick : pick k ∈ P k
      · let p₀ : {p : ℕ // p ∈ P k} := ⟨pick k, hpick⟩
        rw [Finset.sum_eq_single p₀]
        · simpa [p₀] using hatom k hkR (pick k) hpick
        · intro p hp hne
          have hval : p.1 ≠ pick k := by
            intro heq
            apply hne
            exact Subtype.ext heq
          simp [hval]
        · intro hnot
          exact (hnot (Finset.mem_attach (P k) p₀)).elim
      · have hzero :
            (∑ p ∈ (P k).attach,
              if p.1 = pick k then ν k p.1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          have hval : p.1 ≠ pick k := fun heq => hpick (heq ▸ p.2)
          simp [hval]
        rw [hzero]
        exact hΔ
    · rw [if_neg hkR]
      simp only [locWeight, if_neg hkR]
      rw [Finset.sum_coe_sort]
  have hcoordNonneg (k : Fin n) :
      0 ≤ if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
    by_cases hkR : k ∈ R
    · simp [hkR, hΔ]
    · simp only [if_neg hkR]
      exact Finset.sum_nonneg fun p hp => hν k p hp
  have hlocalSumNonneg (k : Fin n) :
      0 ≤ ∑ p : {p : ℕ // p ∈ P k}, locWeight k p :=
    Finset.sum_nonneg fun p hp => by
      by_cases hkR : k ∈ R
      · by_cases heq : p.1 = pick k
        · have hpos := hν k p.1 p.2
          rw [heq] at hpos
          simp [locWeight, hkR, heq, hpos]
        · simp [locWeight, hkR, heq]
      · simp [locWeight, hkR, hν k p.1 p.2]
  calc
    _ = ∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
          ∏ k : Fin n, locWeight k (b k) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hterm b
    _ = ∏ k : Fin n, ∑ p : {p : ℕ // p ∈ P k}, locWeight k p := hsumFactor
    _ ≤ ∏ k : Fin n, if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
          apply Finset.prod_le_prod₀
          · intro k hk
            exact hlocalSumNonneg k
          · intro k hk
            exact hcoord k

end

end ArtinPrimitiveRoots.TypeII.PD
