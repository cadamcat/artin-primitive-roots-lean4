import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaBasics
import Mathlib.Analysis.Complex.SqrtDeriv

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

def continuedEis_slTorus (z : ℂˣ) : SL(2, ℂ) :=
  ⟨!![Complex.sqrt (z : ℂ), 0; 0, (Complex.sqrt (z : ℂ))⁻¹], by
    have hsq : (Complex.sqrt (z : ℂ)) ^ 2 = (z : ℂ) := by
      simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (z : ℂ) 2
    have hr : Complex.sqrt (z : ℂ) ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
      exact z.ne_zero hsq.symm
    rw [Matrix.det_fin_two]
    change Complex.sqrt (z : ℂ) * (Complex.sqrt (z : ℂ))⁻¹ - 0 * 0 = 1
    simpa only [mul_zero, sub_zero] using mul_inv_cancel₀ hr⟩

theorem continuedEis_slTorus_toPGL (z : ℂˣ) :
    Matrix.SpecialLinearGroup.toPGL (continuedEis_slTorus z) =
      (QuotientGroup.mk (diagM ℂ z) : PGL2 ℂ) := by
  have hsq : (Complex.sqrt (z : ℂ)) ^ 2 = (z : ℂ) := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (z : ℂ) 2
  have hr : Complex.sqrt (z : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    exact z.ne_zero hsq.symm
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      (continuedEis_slTorus z)) = Matrix.ProjGenLinGroup.mk (diagM ℂ z)
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (Complex.sqrt (z : ℂ)) hr, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change (!![Complex.sqrt (z : ℂ), 0; 0, (Complex.sqrt (z : ℂ))⁻¹] :
      Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.diagonal (fun _ : Fin 2 => Complex.sqrt (z : ℂ)) =
      !![(z : ℂ), 0; 0, 1]
  rw [← Matrix.smul_eq_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j
  · change Complex.sqrt (z : ℂ) * Complex.sqrt (z : ℂ) = (z : ℂ)
    simpa only [pow_two] using hsq
  · change Complex.sqrt (z : ℂ) * 0 = 0
    exact mul_zero _
  · change Complex.sqrt (z : ℂ) * 0 = 0
    exact mul_zero _
  · change Complex.sqrt (z : ℂ) * (Complex.sqrt (z : ℂ))⁻¹ = 1
    exact mul_inv_cancel₀ hr

end ArtinPrimitiveRoots.A1.Theta
