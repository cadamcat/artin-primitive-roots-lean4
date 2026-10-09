import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedSieve
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.DivisorCount

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS
open ArtinPrimitiveRoots.TypeII

/-- A prime bin costs at most its distinct-divisor multiplicity in each group. -/
theorem conditioned_group_bin_sum_le
    (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (r : ℕ) (N : Finset ℕ)
    (x z b : ℝ) (hx2 : 2 ≤ x) (hb : 0 < b) (hΨ : IsTestFunction Ψ)
    (hN : ∀ n ∈ N, n.Prime ∧ Real.rpow x b < (n : ℝ)) :
    (∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n z) ≤
      (2 / b) * progressionPrimeSum x M c u Ψ r 1 := by
  classical
  have hxpos : 0 < x := by linarith
  have hPer (Q : ℕ) :
      (∑ n ∈ N, if progressionSieveBaseCondition x M c u r Q ∧
          n ∣ c * r * Q + 1 ∧ roughAbove (c * r * Q + 1) z then
        Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) ≤
      (2 / b) * (if progressionSieveBaseCondition x M c u r Q then
        Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) := by
    by_cases hbase : progressionSieveBaseCondition x M c u r Q
    · simp only [hbase, true_and, if_true]
      let d : ℕ := c * r * Q + 1
      change (∑ n ∈ N, if n ∣ d ∧ roughAbove d z then
          Ψ ((d : ℝ) / x) else 0) ≤ (2 / b) * Ψ ((d : ℝ) / x)
      by_cases hzero : Ψ ((d : ℝ) / x) = 0
      · simp [hzero]
      · have hArg : (d : ℝ) / x ∈ Set.Ioo 1 2 := hΨ.2.1 hzero
        have hdUpper : (d : ℝ) < 2 * x := (div_lt_iff₀ hxpos).mp hArg.2
        have hdpos : 0 < d := by dsimp [d]; omega
        let P : Finset ℕ := N.filter (fun n : ℕ => n ∣ d)
        have hP : ∀ n ∈ P, n.Prime ∧ n ∣ d ∧ Real.rpow x b < (n : ℝ) := by
          intro n hn
          rcases Finset.mem_filter.mp hn with ⟨hnN, hnd⟩
          exact ⟨(hN n hnN).1, hnd, (hN n hnN).2⟩
        have hCount := large_prime_divisor_count x b d P hx2 hb hdpos hdUpper hP
        have hPsiNonneg : 0 ≤ Ψ ((d : ℝ) / x) := hΨ.2.2.1 _
        by_cases hrough : roughAbove d z
        · calc
            _ = ∑ n ∈ P, Ψ ((d : ℝ) / x) := by
              dsimp [P]
              rw [Finset.sum_filter]
              simp only [hrough, and_true]
            _ = (P.card : ℝ) * Ψ ((d : ℝ) / x) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (2 / b) * Ψ ((d : ℝ) / x) :=
              mul_le_mul_of_nonneg_right hCount hPsiNonneg
        · simp only [hrough, and_false, if_false, Finset.sum_const_zero]
          exact mul_nonneg (by positivity) hPsiNonneg
    · simp [hbase]
  unfold conditionedSiftedProgressionPrimeSum
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ Q ∈ Finset.range (⌊2 * x⌋₊ + 1),
        (2 / b) * (if progressionSieveBaseCondition x M c u r Q then
          Ψ (((c * r * Q + 1 : ℕ) : ℝ) / x) else 0) :=
      Finset.sum_le_sum (fun Q hQ => hPer Q)
    _ = _ := by
      unfold progressionPrimeSum
      rw [Finset.sum_filter, Finset.mul_sum]
      simp only [one_dvd, and_true, progressionSieveBaseCondition]
      apply Finset.sum_congr rfl
      intro Q hQ
      by_cases hbase : progressionSieveBaseCondition x M c u r Q <;>
        simp only [progressionSieveBaseCondition] at hbase <;>
          simp [hbase]

end ArtinPrimitiveRoots.Proofs.c_bins_sol
