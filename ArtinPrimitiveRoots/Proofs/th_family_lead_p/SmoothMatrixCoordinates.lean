import ArtinPrimitiveRoots.Spec.Geometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
open NumberField Matrix
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- The squared norm of the bottom row, the positive coordinate denominator. -/
def thetaMatrixDenom (m : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (m 1 0) + Complex.normSq (m 1 1)

/-- Upper-half-space coordinates of an invertible complex matrix, invariant under scalars. -/
def thetaMatrixCoord (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ × ℝ :=
  ((m 0 0 * star (m 1 0) + m 0 1 * star (m 1 1)) / (thetaMatrixDenom m : ℂ),
    ‖m.det‖ / thetaMatrixDenom m)

private theorem thetaMatrixDenom_pos (m : Matrix (Fin 2) (Fin 2) ℂ)
    (hm : m.det ≠ 0) : 0 < thetaMatrixDenom m := by
  have hrow : m 1 0 ≠ 0 ∨ m 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (by simp [Matrix.det_fin_two, h.1, h.2])
  rcases hrow with hc | hd
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hc)
      (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (Complex.normSq_pos.mpr hd)

private theorem thetaMatrixCoord_contDiffOn :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) thetaMatrixCoord
      {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} := by
  have he (i j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m : Matrix (Fin 2) (Fin 2) ℂ => m i j) := by fun_prop
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) thetaMatrixDenom := by
    unfold thetaMatrixDenom
    simpa only [Complex.normSq_eq_norm_sq] using
      ((he 1 0).norm_sq ℂ).add ((he 1 1).norm_sq ℂ)
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m : Matrix (Fin 2) (Fin 2) ℂ =>
        m 0 0 * star (m 1 0) + m 0 1 * star (m 1 1)) := by
    have hc (i j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun m : Matrix (Fin 2) (Fin 2) ℂ => star (m i j)) := by
      exact Complex.conjCLE.contDiff.comp (he i j)
    exact ((he 0 0).mul (hc 1 0)).add ((he 0 1).mul (hc 1 1))
  have hdet : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have hd0 : ∀ m : Matrix (Fin 2) (Fin 2) ℂ, m.det ≠ 0 → thetaMatrixDenom m ≠ 0 :=
    fun m hm => (thetaMatrixDenom_pos m hm).ne'
  intro m hm
  have hdx := (Complex.ofRealCLM.contDiff.comp hd).contDiffAt.fun_inv
    (Complex.ofReal_ne_zero.mpr (hd0 m hm))
  have hdy := hd.contDiffAt.fun_inv (hd0 m hm)
  have hx := hnum.contDiffAt.mul hdx
  have hy := (hdet.contDiffAt.norm ℂ hm).mul hdy
  unfold thetaMatrixCoord
  simpa only [div_eq_mul_inv, Function.comp_apply, Complex.ofRealCLM_apply] using
    (hx.prodMk hy).contDiffWithinAt

private theorem thetaMatrixCoord_eq_spec (g : SL(2, ℂ)) :
    thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (ArtinPrimitiveRoots.A1.Spec.horiz (QuotientGroup.mk g),
        ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk g)) := by
  apply Prod.ext
  · simp [thetaMatrixCoord, thetaMatrixDenom,
      ArtinPrimitiveRoots.A1.Spec.horiz, ArtinPrimitiveRoots.A1.Spec.herm,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj]
  · simp [thetaMatrixCoord, thetaMatrixDenom,
      ArtinPrimitiveRoots.A1.Spec.height, ArtinPrimitiveRoots.A1.Spec.herm,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.mul_conj,
      g.det_coe, one_div]

variable {F : Type} [Field F] [NumberField F]

/-- The open set of archimedean matrix parameters used for smooth adelic charts. -/
def thetaMatrixRegion : Set (InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) :=
  {m | ∀ w, (m w).det ≠ 0}

/-- The product of the explicit upper-half-space coordinate maps. -/
def thetaMatrixCoords (m : InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ) :
    ArtinPrimitiveRoots.A1.Spec.Coord F := fun w => thetaMatrixCoord (m w)

/-- Matrix coordinates are smooth on the full invertible locus and have positive height.
On determinant-one representatives they are exactly the frozen classical coordinates. -/
theorem theta_matrix_coordinates_regular :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (thetaMatrixCoords (F := F)) thetaMatrixRegion ∧
    (∀ m ∈ thetaMatrixRegion (F := F),
      thetaMatrixCoords m ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) ∧
    ∀ g : InfinitePlace F → SL(2, ℂ),
      thetaMatrixCoords (fun w => (g w : Matrix (Fin 2) (Fin 2) ℂ)) =
        ArtinPrimitiveRoots.A1.Spec.coordsX F
          (fun w => (QuotientGroup.mk (g w) : ArtinPrimitiveRoots.A1.Spec.H3)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro w
    have he : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun m : InfinitePlace F → Matrix (Fin 2) (Fin 2) ℂ => m w) := by fun_prop
    exact thetaMatrixCoord_contDiffOn.comp he.contDiffOn (fun m hm => hm w)
  · intro m hm w
    exact div_pos (norm_pos_iff.mpr (hm w)) (thetaMatrixDenom_pos (m w) (hm w))
  · intro g
    funext w
    exact thetaMatrixCoord_eq_spec (g w)

end ArtinPrimitiveRoots.A1.Theta
