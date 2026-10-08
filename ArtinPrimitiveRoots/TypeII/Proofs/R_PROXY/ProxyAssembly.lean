import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.PhaseBounds

/-!
Finite divisor-mass and residue-class assembly for the rough proxy source.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- The retained inclusion-exclusion divisors have reciprocal mass at most
`1/V(W)`. -/
theorem truncated_divisor_reciprocal_mass_le_inv_sieve_product
    (W : ℝ) (r : ℕ) :
    (∑ S ∈ (primesUpTo W).powerset.filter (fun S => S.card < r),
      1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤
      (roughSieveProduct W)⁻¹ := by
  classical
  let P := primesUpTo W
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    exact (Finset.mem_filter.mp hp).2
  have hterm (p : ℕ) (hp : p ∈ P) :
      1 + 1 / (p : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    have hpPrime := hPprime p hp
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hrecipPos : 0 < 1 / (p : ℝ) := by positivity
    have hrecipLe : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hpCast
    have hfactorPos : 0 < 1 - 1 / (p : ℝ) := by linarith
    rw [← one_div]
    apply (le_div_iff₀ hfactorPos).2
    nlinarith [sq_nonneg (1 / (p : ℝ))]
  have hEuler :
      (∏ p ∈ P, (1 + 1 / (p : ℝ))) ≤
        ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      exact hterm p hp
  have hInv :
      (∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹) =
        (∏ p ∈ P, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
  have hMass := truncated_divisor_reciprocal_mass P
    (fun p hp => hPprime p hp) r
  calc
    _ ≤ ∏ p ∈ P, (1 + 1 / (p : ℝ)) := hMass
    _ ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := hEuler
    _ = (roughSieveProduct W)⁻¹ := by
      rw [hInv]
      simp [P, roughSieveProduct]

/-- Sum the per-residue phase estimates over all retained subset divisors.
The hypotheses isolate the analytic estimate from the finite reindexing. -/
theorem truncated_source_interval_norm_bound
    (x u M V B : ℝ) (r k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (l rr : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hB : 0 ≤ B)
    (hl : M ≤ l) (hlr : l ≤ rr) (hr : rr ≤ 2 * M)
    (hMass :
      (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤ 1 / V)
    (hResidue : ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
        (fun S => S.card < r), ∀ a : ZMod k,
        ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) k a u
            (l / ((∏ p ∈ S, p : ℕ) : ℝ))
            (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
          B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) :
    ‖∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
        (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
        (smallPrimeTruncation x r m : ℂ) *
          ((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ))‖ ≤ B * M / V := by
  sorry

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
