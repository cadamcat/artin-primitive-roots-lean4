import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ProgressionSieve

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open ArtinPrimitiveRoots.Construction
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS
open ArtinPrimitiveRoots.TypeII

/-- Sum the per-group sieve bounds using a common lower bound for the sieve product. -/
theorem weighted_sifted_sum_lower
    (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (R : Finset ℕ) (x z D alpha P B : ℝ)
    (hΨ : IsTestFunction Ψ) (hAlpha : 0 ≤ alpha)
    (hProduct : ∀ r ∈ R, P ≤ progressionSieveProductFor M r z)
    (hSieve : ∀ r ∈ R,
      alpha * progressionPrimeSum x M c u Ψ r 1 *
          progressionSieveProductFor M r z -
        B * (∑ ℓ ∈ oddSquarefreeUpTo D,
          |progressionPrimeSum x M c u Ψ r ℓ -
            localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) ≤
        siftedProgressionPrimeSum x M c u Ψ r z) :
    alpha * P * (∑ r ∈ R,
        markedWeight x K a (1 / 2 : ℝ) r * progressionPrimeSum x M c u Ψ r 1) -
      B * (∑ r ∈ R, ∑ ℓ ∈ oddSquarefreeUpTo D,
        markedWeight x K a (1 / 2 : ℝ) r *
          |progressionPrimeSum x M c u Ψ r ℓ -
            localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) ≤
      ∑ r ∈ R, markedWeight x K a (1 / 2 : ℝ) r *
        siftedProgressionPrimeSum x M c u Ψ r z := by
  classical
  calc
    _ = ∑ r ∈ R,
        (alpha * P * (markedWeight x K a (1 / 2 : ℝ) r *
            progressionPrimeSum x M c u Ψ r 1) -
          B * ∑ ℓ ∈ oddSquarefreeUpTo D,
            markedWeight x K a (1 / 2 : ℝ) r *
              |progressionPrimeSum x M c u Ψ r ℓ -
                localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      have hW : 0 ≤ markedWeight x K a (1 / 2 : ℝ) r :=
        markedWeight_nonneg x K a (1 / 2 : ℝ) r (by norm_num)
      have hA : 0 ≤ progressionPrimeSum x M c u Ψ r 1 := by
        unfold progressionPrimeSum
        exact Finset.sum_nonneg (fun Q _ => hΨ.2.2.1 _)
      have hProductMul :
          alpha * P * (markedWeight x K a (1 / 2 : ℝ) r *
              progressionPrimeSum x M c u Ψ r 1) ≤
            markedWeight x K a (1 / 2 : ℝ) r *
              (alpha * progressionPrimeSum x M c u Ψ r 1 *
                progressionSieveProductFor M r z) := by
        have h := mul_le_mul_of_nonneg_left (hProduct r hr)
          (mul_nonneg hW (mul_nonneg hAlpha hA))
        convert h using 1 <;> ring
      calc
        _ ≤ markedWeight x K a (1 / 2 : ℝ) r *
              (alpha * progressionPrimeSum x M c u Ψ r 1 *
                progressionSieveProductFor M r z) -
            B * ∑ ℓ ∈ oddSquarefreeUpTo D,
              markedWeight x K a (1 / 2 : ℝ) r *
                |progressionPrimeSum x M c u Ψ r ℓ -
                  localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1| :=
          sub_le_sub_right hProductMul _
        _ = markedWeight x K a (1 / 2 : ℝ) r *
            (alpha * progressionPrimeSum x M c u Ψ r 1 *
                progressionSieveProductFor M r z -
              B * ∑ ℓ ∈ oddSquarefreeUpTo D,
                |progressionPrimeSum x M c u Ψ r ℓ -
                  localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) := by
          rw [← Finset.mul_sum]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hSieve r hr) hW

end ArtinPrimitiveRoots.Proofs.c_bins_sol
