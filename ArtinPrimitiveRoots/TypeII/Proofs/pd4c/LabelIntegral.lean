import ArtinPrimitiveRoots.TypeII.Defs
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII MeasureTheory

noncomputable section

/-- Integer characters are orthogonal to the constant character on one period. -/
theorem integer_character_integral (n : ℤ) :
    (∫ θ in (0 : ℝ)..1, additiveCharacter ((n : ℝ)*θ)) =
      if n = 0 then 1 else 0 := by
  letI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) 0) (-n)
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at h
  simp only [div_one, zero_add, one_smul, neg_neg, fourier_zero, smul_eq_mul, mul_one] at h
  have hchar (θ : ℝ) : @fourier (1 : ℝ) n (θ : AddCircle (1 : ℝ)) =
      additiveCharacter ((n : ℝ)*θ) := by
    rw [fourier_coe_apply]
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  simpa only [hchar, Pi.single_apply, neg_eq_zero, eq_comm] using h

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
