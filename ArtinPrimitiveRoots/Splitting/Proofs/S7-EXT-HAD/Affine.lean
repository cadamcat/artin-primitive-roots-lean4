import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-HAD».Infrastructure.Analysis.Complex.HadamardFactorization.Growth

import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- An order-one entire function is an affine exponential times its divisor product. -/
theorem hadamard_affine_divisor_product (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ A B : ℂ, ∀ s : ℂ, G s = Complex.exp (A + B * s) *
      Port.Complex.Hadamard.divisorCanonicalProduct 1 G Set.univ s := by
  obtain ⟨C, hC, hbound⟩ := hgrowth
  have hpower : ∀ s : ℂ, ‖G s‖ ≤
      Real.exp ((4 * C) * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
    intro s
    have hlog : Real.log (‖s‖ + 2) ≤ 4 * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
      have hp : (‖s‖ + 2) ^ (1 / 2 : ℝ) ≤
          2 * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
        calc
          _ ≤ (4 * (1 + ‖s‖)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg s]) (by norm_num)
          _ = _ := by
            rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
            rw [← Real.sqrt_eq_rpow]
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      have hl := Real.log_le_rpow_div (show (0 : ℝ) ≤ ‖s‖ + 2 by positivity)
        (show (0 : ℝ) < 1 / 2 by norm_num)
      linarith
    have hpow : (1 + ‖s‖) ^ (3 / 2 : ℝ) =
        (1 + ‖s‖) * (1 + ‖s‖) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by positivity), Real.rpow_one]
    refine (hbound s).trans (Real.exp_le_exp.mpr ?_)
    calc
      C * (‖s‖ + 1) * Real.log (‖s‖ + 2) ≤
          C * (‖s‖ + 1) * (4 * (1 + ‖s‖) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (4 * C) * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by rw [hpow]; ring
  have hloggrowth := Port.Real.log_growth_of_norm_le_exp_mul_rpow
    (f := G) (r := fun s : ℂ => 1 + ‖s‖) (τ := (3 / 2 : ℝ))
    (show 0 < 4 * C by positivity) (by norm_num)
    (fun s => by linarith [norm_nonneg s]) hpower
  obtain ⟨P, hdeg, hfac⟩ := Port.Complex.Hadamard.hadamard_factorization_of_growth
    (ρ := (3 / 2 : ℝ)) (by norm_num) hG ⟨0, hG0⟩ hloggrowth
  have hfloor : Nat.floor (3 / 2 : ℝ) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr
    norm_num
  have hdeg1 : P.degree ≤ 1 := by simpa [hfloor] using hdeg
  have hord0 : analyticOrderNatAt G 0 = 0 := by
    by_contra h
    exact hG0 (apply_eq_zero_of_analyticOrderNatAt_ne_zero h)
  refine ⟨P.coeff 0, P.coeff 1, fun s => ?_⟩
  have heval : Polynomial.eval s P = P.coeff 0 + P.coeff 1 * s := by
    have hp := congrArg (Polynomial.eval s) (Polynomial.eq_X_add_C_of_degree_le_one hdeg1)
    simpa [add_comm] using hp
  simpa [heval, hord0, hfloor] using hfac s

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
