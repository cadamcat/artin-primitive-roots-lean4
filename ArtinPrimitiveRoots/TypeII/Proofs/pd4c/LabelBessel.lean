import ArtinPrimitiveRoots.TypeII.Defs
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII MeasureTheory

noncomputable section

/-- A finite part of the label Fourier coefficients is bounded by the full energy. -/
theorem finite_label_bessel_bound (U : Finset ℤ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    (∑ n ∈ U, ‖∫ θ in (0 : ℝ)..1,
      additiveCharacter (-(n : ℝ)*θ)*f θ‖^2) ≤
      ∫ θ in (0 : ℝ)..1, ‖f θ‖^2 := by
  have hab : (0 : ℝ) < 1 := by norm_num
  have hcoeff (n : ℤ) : fourierCoeffOn hab f n =
      ∫ θ in (0 : ℝ)..1, additiveCharacter (-(n : ℝ)*θ)*f θ := by
    rw [fourierCoeffOn_eq_integral]
    simp_rw [fourier_coe_apply]
    simp only [sub_zero, div_one, one_smul, smul_eq_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only
    congr 1
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  have hsum := hasSum_sq_fourierCoeffOn hab hf
  have hbound := hsum.summable.sum_le_tsum U (fun n hn => sq_nonneg ‖fourierCoeffOn hab f n‖)
  rw [hsum.tsum_eq] at hbound
  simp only [sub_zero, inv_one, one_smul] at hbound
  simpa only [hcoeff] using hbound

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
