import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CircleInverseSum
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The finite separated-phase estimate yields a logarithmic reciprocal-distance bound. -/
theorem circle_inverse_log_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (d : ℕ) (B : ℝ)
    (hd : 2 ≤ d) (hB : 0 ≤ B)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      1/(2*(d:ℝ)) ≤ circleDistance (φ i-φ j)) :
    (∑ i ∈ T, if circleDistance (φ i)=0 then B
      else min B (1/circleDistance (φ i))) ≤
    B+16*(d:ℝ)*(1+Real.log (4*(d:ℝ))) := by
  have hfinite := circle_inverse_sum_bound T φ d B hd hB hsep
  have hharm : (∑ j ∈ Finset.Icc 1 (4*d), 1/(j:ℝ)) ≤
      1+Real.log (4*(d:ℝ)) := by
    have h := harmonic_le_one_add_log (4*d)
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      one_div, Nat.cast_mul, Nat.cast_ofNat] using h
  have hm : 16*(d:ℝ)*(∑ j ∈ Finset.Icc 1 (4*d), 1/(j:ℝ)) ≤
      16*(d:ℝ)*(1+Real.log (4*(d:ℝ))) :=
    mul_le_mul_of_nonneg_left hharm (by positivity)
  exact hfinite.trans (add_le_add (le_refl B) hm)

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
