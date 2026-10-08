import ArtinPrimitiveRoots.Spec.Geometry
import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

/-- The Iwasawa coordinates of a special-linear translate are its actual hyperbolic coordinates. -/
theorem th_classical_sl_reconstruction (g : SL(2, ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y) :
    ∃ k : GL (Fin 2) ℂ,
      (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      ∃ hy' : 0 < Spec.height (g • Spec.pt x y),
        (QuotientGroup.mk (g : GL (Fin 2) ℂ) : PGL2 ℂ) *
            QuotientGroup.mk (upperM ℂ x * diagM ℂ
              (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) =
          QuotientGroup.mk (upperM ℂ (Spec.horiz (g • Spec.pt x y)) * diagM ℂ
            (Units.mk0 (Spec.height (g • Spec.pt x y) : ℂ)
              (Complex.ofReal_ne_zero.mpr hy'.ne')) * k) := by
  have hsection (u : ℂ) (v : ℝ) (hv : 0 < v) :
      (QuotientGroup.mk (Spec.ptMat u v hv : GL (Fin 2) ℂ) : PGL2 ℂ) =
        QuotientGroup.mk (upperM ℂ u * diagM ℂ
          (Units.mk0 (v : ℂ) (Complex.ofReal_ne_zero.mpr hv.ne'))) := by
    have hroot : (Real.sqrt v : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
    change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨Units.mk0 (Real.sqrt v : ℂ) hroot, ?_⟩
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.diagonal, Matrix.scalar, Spec.ptMat, upperM, diagM,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
        Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
      <;> field_simp [hroot]
      <;> norm_num [Real.mul_self_sqrt hv.le]
      <;> rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
  let z : Spec.H3 := g • Spec.pt x y
  let h : SL(2, ℂ) := g * Spec.ptMat x y hy
  have hz : z = (QuotientGroup.mk h : Spec.H3) := by
    simp only [z, Spec.pt, dif_pos hy]
    rfl
  have hy' : 0 < Spec.height z := by
    rw [Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos z
  let a : SL(2, ℂ) := Spec.ptMat (Spec.horiz z) (Spec.height z) hy'
  have hpoint : (QuotientGroup.mk a : Spec.H3) = QuotientGroup.mk h := by
    simpa only [Spec.pt, dif_pos hy'] using (Spec.pt_horiz_height z).trans hz
  let k : SL(2, ℂ) := a⁻¹ * h
  have hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hpoint)
  refine ⟨(k : GL (Fin 2) ℂ), hk, hy', ?_⟩
  rw [← hsection x y hy, QuotientGroup.mk_mul,
    ← hsection (Spec.horiz z) (Spec.height z) hy',
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  apply congrArg (fun t : GL (Fin 2) ℂ => (QuotientGroup.mk t : PGL2 ℂ))
  change Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL (Spec.ptMat x y hy) =
    Matrix.SpecialLinearGroup.toGL a * Matrix.SpecialLinearGroup.toGL (a⁻¹ * h)
  rw [← map_mul, ← map_mul, mul_inv_cancel_left]

end ArtinPrimitiveRoots.A1.Theta
