import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedSieve

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical
open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS
open ArtinPrimitiveRoots.TypeII

/-- Aggregate the conditioned sieve with the nonnegative marked weights. -/
theorem weighted_conditioned_sieve_sum_approx
    (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (R N : Finset ℕ) (x z D α B : ℝ)
    (hSieve : ∀ r ∈ R,
      |(∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n z) -
        (progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z *
          (∑ n ∈ N, 1 / ((n : ℝ) - 1)))| ≤
        α * (progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z *
          (∑ n ∈ N, 1 / ((n : ℝ) - 1))) +
          B * ∑ ℓ ∈ oddSquarefreeUpTo D,
            |progressionPrimeSum x M c u Ψ r ℓ -
              localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) :
    |(∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
        (∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n z)) -
      ((∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
          progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z) *
        (∑ n ∈ N, 1 / ((n : ℝ) - 1)))| ≤
      α * ((∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
          progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z) *
        (∑ n ∈ N, 1 / ((n : ℝ) - 1))) +
        B * (∑ r ∈ R, ∑ ℓ ∈ oddSquarefreeUpTo D,
          markedWeight x K a (1 / 2 : ℝ) r *
            |progressionPrimeSum x M c u Ψ r ℓ -
              localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) := by
  classical
  let w : ℕ → ℝ := fun r => markedWeight x K a (1 / 2 : ℝ) r
  let Q : ℝ := ∑ n ∈ N, 1 / ((n : ℝ) - 1)
  let S : ℕ → ℝ := fun r =>
    ∑ n ∈ N, conditionedSiftedProgressionPrimeSum x M c u Ψ r n z
  let A : ℕ → ℝ := fun r =>
    progressionPrimeSum x M c u Ψ r 1 * progressionSieveProductFor M r z
  let Err : ℕ → ℝ := fun r => ∑ ℓ ∈ oddSquarefreeUpTo D,
    |progressionPrimeSum x M c u Ψ r ℓ -
      localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|
  have hW (r : ℕ) : 0 ≤ w r :=
    markedWeight_nonneg x K a (1 / 2 : ℝ) r (by norm_num)
  have hPer : ∀ r ∈ R, |S r - A r * Q| ≤ α * (A r * Q) + B * Err r := hSieve
  have hMain : (∑ r ∈ R, w r * A r) * Q = ∑ r ∈ R, w r * (A r * Q) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hTotal : |(∑ r ∈ R, w r * S r) - (∑ r ∈ R, w r * A r) * Q| ≤
      α * ((∑ r ∈ R, w r * A r) * Q) + B * (∑ r ∈ R, w r * Err r) := by
    calc
      _ = |∑ r ∈ R, w r * (S r - A r * Q)| := by
        rw [hMain]
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ r ∈ R, |w r * (S r - A r * Q)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ R, w r * (α * (A r * Q) + B * Err r) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [abs_mul, abs_of_nonneg (hW r)]
        exact mul_le_mul_of_nonneg_left (hPer r hr) (hW r)
      _ = _ := by
        rw [hMain]
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro r hr
          ring
        · apply Finset.sum_congr rfl
          intro r hr
          ring
  have hErrorSum : (∑ r ∈ R, w r * Err r) =
      ∑ r ∈ R, ∑ ℓ ∈ oddSquarefreeUpTo D,
        w r * |progressionPrimeSum x M c u Ψ r ℓ -
          localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1| := by
    simp only [Err, Finset.mul_sum]
  rw [hErrorSum] at hTotal
  simpa only [w, S, A, Q, mul_assoc] using hTotal

end ArtinPrimitiveRoots.Proofs.c_bins_sol
