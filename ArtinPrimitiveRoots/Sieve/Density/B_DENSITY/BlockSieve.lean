import Mathlib
import ArtinPrimitiveRoots.Sieve.Block
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Counting

/-! Uniform block-sieve estimates for the density comparison. -/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

/-- Uniform block-sieve error bound for the interval `(x,2x]` with divisibility conditions by
primes up to `z`. Its small-product error is bounded separately by counting prime products. -/
lemma roughIntegerCount_le_block :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℕ, ∀ (z : ℝ), 2 ≤ z → ∀ (x : ℝ), 0 ≤ x → ∀ H : ℕ,
      Even H → H₀ ≤ H →
      |roughIntegerCount x z - x * ∏ p ∈ roughSievePrimes z, (1 - 1 / (p : ℝ))| ≤
        K * Real.exp (-(H : ℝ)) *
            (x * ∏ p ∈ roughSievePrimes z, (1 - 1 / (p : ℝ))) +
          K * ∑ D ∈ (roughSievePrimes z).powerset with
            ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2),
            |(∑ n ∈ roughIntegerInterval x with ∀ p ∈ D, p ∣ n, (1 : ℝ)) -
              x * ∏ p ∈ D, (1 / (p : ℝ))| := by
  classical
  obtain ⟨C₀, hC₀, hband⟩ := exists_prime_reciprocal_band_bound
  obtain ⟨K, hK, H₀, hblock⟩ :=
    ArtinPrimitiveRoots.Sieve.lem_block (η₀ := 1 / 2) C₀ (by norm_num)
  refine ⟨K, hK, H₀, ?_⟩
  intro z hz x hx H hHeven hH
  let A := roughIntegerInterval x
  let P := roughSievePrimes z
  let bad : ℕ → ℕ → Prop := fun p n => p ∣ n
  let g : ℕ → ℝ := fun p => 1 / (p : ℝ)
  have hwt : ∀ n ∈ A, 0 ≤ (1 : ℝ) := by intro n hn; norm_num
  have hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z := by
    intro p hp
    simp only [P, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    refine ⟨hp.2, ?_⟩
    have hz0 : 0 ≤ z := by linarith
    exact (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le hz0)
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - (1 / 2 : ℝ) := by
    intro p hp
    have hpPrime : p.Prime := (hP p hp).1
    have hp2 : 2 ≤ p := hpPrime.two_le
    constructor
    · dsimp [g]
      positivity
    · have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      dsimp [g]
      rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by ring]
      exact (one_div_le_one_div_of_le (by norm_num) hpcast)
  have hlocal : ∀ v : ℝ, 1 < v →
      ∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀ := by
    intro v hv
    have hsubset :
        P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2) ⊆
          ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => v < (p : ℝ)) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpCond⟩
      rcases hpCond with ⟨hvlt, hpv⟩
      have hv20 : 0 ≤ v ^ 2 := sq_nonneg v
      have hpP' : (2 ≤ p ∧ p ≤ ⌊z⌋₊) ∧ p.Prime := by
        simpa [P, roughSievePrimes, Finset.mem_filter, Finset.mem_Icc] using hpP
      apply Finset.mem_filter.mpr
      refine ⟨?_, hvlt⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hpP'.1.1, ?_⟩, hpP'.2⟩
      exact (Nat.le_floor_iff hv20).2 hpv
    have hsum :
        (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p) ≤
          ∑ p ∈ ((Finset.Icc 2 ⌊v ^ 2⌋₊).filter Nat.Prime).filter
            (fun p : ℕ => v < (p : ℝ)), g p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpB
      change 0 ≤ 1 / (p : ℝ)
      positivity
    exact hsum.trans (by simpa [g] using hband v hv)
  have happly := hblock ℕ A (fun _ => (1 : ℝ)) hwt z hz P hP bad x g hx hg hlocal
  have hfirst := happly.1 H hHeven hH
  simpa [roughIntegerCount, A, P, bad, g, mul_assoc, mul_left_comm, mul_comm] using hfirst

end ArtinPrimitiveRoots.Proofs.b_density_sol
