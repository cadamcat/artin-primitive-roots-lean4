import ArtinPrimitiveRoots.Proofs.th_continue_b.ThetaBasics
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

def continuedEis_archExp (S : SData F CE condη) (t : InfinitePlace F → ℂ) : S.FSˣ where
  val := (1, fun w => Complex.exp (t w))
  inv := (1, fun w => Complex.exp (-(t w)))
  val_inv := by
    apply Prod.ext
    · exact one_mul _
    · funext w
      change Complex.exp (t w) * Complex.exp (-(t w)) = 1
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    apply Prod.ext
    · exact one_mul _
    · funext w
      change Complex.exp (-(t w)) * Complex.exp (t w) = 1
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

def continuedEis_slTorusExp (t : ℂ) : SL(2, ℂ) :=
  ⟨!![Complex.exp (t / 2), 0; 0, Complex.exp (-(t / 2))], by
    rw [Matrix.det_fin_two]
    change Complex.exp (t / 2) * Complex.exp (-(t / 2)) - 0 * 0 = 1
    rw [mul_zero, sub_zero, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]⟩

theorem continuedEis_slTorusExp_toPGL (t : ℂ) :
    Matrix.SpecialLinearGroup.toPGL (continuedEis_slTorusExp t) =
      (QuotientGroup.mk (diagM ℂ
        (Units.mk0 (Complex.exp t) (Complex.exp_ne_zero t))) : PGL2 ℂ) := by
  have hsq : Complex.exp (t / 2) * Complex.exp (t / 2) = Complex.exp t := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hpair : Complex.exp (t / 2) * Complex.exp (-(t / 2)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      (continuedEis_slTorusExp t)) = Matrix.ProjGenLinGroup.mk (diagM ℂ _)
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (Complex.exp (t / 2)) (Complex.exp_ne_zero (t / 2)), ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change (!![Complex.exp (t / 2), 0; 0, Complex.exp (-(t / 2))] :
      Matrix (Fin 2) (Fin 2) ℂ) *
      Matrix.diagonal (fun _ : Fin 2 => Complex.exp (t / 2)) =
      !![Complex.exp t, 0; 0, 1]
  rw [← Matrix.smul_eq_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j
  · exact hsq
  · exact mul_zero _
  · exact mul_zero _
  · exact hpair

end ArtinPrimitiveRoots.A1.Theta
