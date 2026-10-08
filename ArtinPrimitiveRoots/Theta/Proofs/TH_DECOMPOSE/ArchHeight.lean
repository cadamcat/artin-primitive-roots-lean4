import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.UnitaryScalar

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

/-- The spherical complex section equals the corresponding hyperbolic height power. -/
theorem sphC_sl2_height (s : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : ℂ) (y : ℝ) (hy : 0 < y) :
    sphC s (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
      QuotientGroup.mk (upperM ℂ x) *
      QuotientGroup.mk (diagM ℂ (Units.mk0 (y : ℂ)
        (Complex.ofReal_ne_zero.mpr hy.ne')))) =
      (ArtinPrimitiveRoots.A1.Spec.height
        (γ • ArtinPrimitiveRoots.A1.Spec.pt x y) : ℂ) ^ (1 + 2 * s) := by
  let u : ℂˣ := Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')
  let a := Matrix.SpecialLinearGroup.toGL γ * upperM ℂ x * diagM ℂ u
  have ha : (a : Matrix (Fin 2) (Fin 2) ℂ) =
      (γ : Matrix (Fin 2) (Fin 2) ℂ) * !![1, x; 0, 1] * !![(y : ℂ), 0; 0, 1] := by
    rfl
  have hdet : (a : Matrix (Fin 2) (Fin 2) ℂ).det = (y : ℂ) := by
    rw [ha, Matrix.det_mul, Matrix.det_mul, γ.det_coe]
    simp [Matrix.det_fin_two]
  have hrow0 : (a : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = γ 1 0 * (y : ℂ) := by
    rw [ha]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrow1 : (a : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = γ 1 0 * x + γ 1 1 := by
    rw [ha]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_of_nonneg hy.le]
  have hbase : ‖(a : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(a : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(a : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) =
      ArtinPrimitiveRoots.A1.Spec.height (γ • ArtinPrimitiveRoots.A1.Spec.pt x y) := by
    rw [hdet, hrow0, hrow1, ArtinPrimitiveRoots.A1.Spec.height_smul_pt γ x y hy,
      norm_mul, hny]
    simp only [Complex.normSq_eq_norm_sq]
    congr 1
    ring
  have hq : QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
      QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ u) =
      (QuotientGroup.mk a : PGL2 ℂ) := by
    simp only [a, QuotientGroup.mk_mul]
  change sphC s (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
    QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ u)) = _
  rw [hq, sphC_mk]
  unfold sphericalC
  rw [hbase]

end ArtinPrimitiveRoots.A1.Theta
