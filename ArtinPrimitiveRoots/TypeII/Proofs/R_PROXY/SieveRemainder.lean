import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra

/-!
Finite summation of the pointwise truncated-sieve remainder.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- Sum the pointwise truncated-sieve error over any finite set of positive
integers bounded by `2M`. -/
theorem sieve_remainder_sum_bound (x M : ℝ) (r : ℕ)
    (I : Finset ℕ) (hM : 0 < M)
    (hI : ∀ m ∈ I, 0 < m ∧ (m : ℝ) ≤ 2 * M) (hr : 1 ≤ r) :
    ∑ m ∈ I,
      |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
        smallPrimeTruncation x r m| ≤
      2 * M *
        (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
            (fun S => S.card = r),
          1 / ((∏ p ∈ S, p : ℕ) : ℝ)) := by
  classical
  let P := primesUpTo (roughCutoff x)
  let Q := P.powerset.filter (fun S => S.card = r)
  have hpoint (m : ℕ) (hm : m ∈ I) :
      |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m| ≤
        ∑ S ∈ Q, if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := by
    simpa [P, Q] using
      sieve_remainder_pointwise x r m hr (hI m hm).1
  have hsumSwap :
      (∑ m ∈ I, ∑ S ∈ Q,
          if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0) =
        ∑ S ∈ Q, ∑ m ∈ I,
          if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
  calc
    _ ≤ ∑ m ∈ I, ∑ S ∈ Q,
          if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            exact hpoint m hm
    _ = ∑ S ∈ Q, ∑ m ∈ I,
          if (∏ p ∈ S, p) ∣ m then (1 : ℝ) else 0 := hsumSwap
    _ ≤ ∑ S ∈ Q, 2 * M / ((∏ p ∈ S, p : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro S hS
          have hSP : S ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
          have hd : 0 < (∏ p ∈ S, p : ℕ) := by
            apply Finset.prod_pos
            intro p hp
            have hpP : p ∈ P := hSP hp
            have hpPrime : p.Prime := by
              dsimp [P, primesUpTo] at hpP
              exact (Finset.mem_filter.mp hpP).2
            exact hpPrime.pos
          have hcount := positive_multiple_count_bound M
            (∏ p ∈ S, p : ℕ) hM hd I hI
          exact hcount
    _ = 2 * M *
        (∑ S ∈ Q, 1 / ((∏ p ∈ S, p : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          ring
    _ = 2 * M *
        (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
            (fun S => S.card = r),
          1 / ((∏ p ∈ S, p : ℕ) : ℝ)) := by rfl

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
