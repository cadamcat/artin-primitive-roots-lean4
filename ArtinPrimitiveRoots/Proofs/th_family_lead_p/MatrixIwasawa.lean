import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SmoothMatrixCoordinates
import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false
open NumberField Matrix
open scoped Classical MatrixGroups Matrix.Norms.Elementwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol
open ArtinPrimitiveRoots.A1.Theta

private theorem theta_matrix_scalar_invariant (c : ℂ) (hc : c ≠ 0)
    (m : Matrix (Fin 2) (Fin 2) ℂ) :
    thetaMatrixCoord (c • m) = thetaMatrixCoord m := by
  have hq : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hd : thetaMatrixDenom (c • m) = Complex.normSq c * thetaMatrixDenom m := by
    simp only [thetaMatrixDenom, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul]
    ring
  have hn : (c * m 0 0 * star (c * m 1 0) + c * m 0 1 * star (c * m 1 1)) =
      (Complex.normSq c : ℂ) * (m 0 0 * star (m 1 0) + m 0 1 * star (m 1 1)) := by
    rw [← Complex.mul_conj c]
    simp only [star_mul]
    change c * m 0 0 * (star (m 1 0) * star c) +
      c * m 0 1 * (star (m 1 1) * star c) =
      c * star c * (m 0 0 * star (m 1 0) + m 0 1 * star (m 1 1))
    ring
  have hdet : ‖(c • m).det‖ = Complex.normSq c * ‖m.det‖ := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, norm_mul, norm_pow, Complex.normSq_eq_norm_sq]
  apply Prod.ext
  · change (c * m 0 0 * star (c * m 1 0) + c * m 0 1 * star (c * m 1 1)) /
        (thetaMatrixDenom (c • m) : ℂ) = _
    rw [hn, hd, Complex.ofReal_mul]
    exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hq)
  · change ‖(c • m).det‖ / thetaMatrixDenom (c • m) = _
    rw [hdet, hd]
    exact mul_div_mul_left _ _ hq

private theorem theta_ptMat_pgl (x : ℂ) (y : ℝ) (hy : 0 < y) :
    (QuotientGroup.mk
      (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy : GL (Fin 2) ℂ) : PGL2 ℂ) =
      QuotientGroup.mk (upperM ℂ x * diagM ℂ
        (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hroot : (Real.sqrt y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt.ne'
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (Real.sqrt y : ℂ) hroot, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.diagonal, Matrix.scalar, ArtinPrimitiveRoots.A1.Spec.ptMat,
      upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Complex.ofReal_mul,
      Real.mul_self_sqrt hy.le]
    <;> field_simp [hroot]
    <;> norm_num [Real.mul_self_sqrt hy.le]
    <;> rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]

/-- The smooth matrix coordinates give the actual PGL Iwasawa decomposition. -/
theorem theta_matrix_pgl_iwasawa (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : GL (Fin 2) ℂ) :
    ∃ hy : 0 < (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2,
      ∃ k : GL (Fin 2) ℂ,
        (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        (QuotientGroup.mk g : PGL2 ℂ) =
          QuotientGroup.mk (upperM ℂ (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).1 *
            diagM ℂ (Units.mk0 ((thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2 : ℂ)
              (Complex.ofReal_ne_zero.mpr hy.ne')) * k) := by
  let e : PGL(2, ℂ) ≃* PSL(2, ℂ) :=
    Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
  obtain ⟨s, hs⟩ : ∃ s : SL(2, ℂ), (QuotientGroup.mk s : PSL(2, ℂ)) =
      e (Matrix.ProjGenLinGroup.mk g) := Quotient.mk_surjective _
  have hsg : Matrix.ProjGenLinGroup.mk (s : GL (Fin 2) ℂ) =
      Matrix.ProjGenLinGroup.mk g := by
    calc
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk s) := rfl
      _ = Matrix.ProjectiveSpecialLinearGroup.toPGL
          (e (Matrix.ProjGenLinGroup.mk g)) := congrArg _ hs
      _ = _ := e.symm_apply_apply _
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hsg
  have hmatrix : (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (c : ℂ) • (s : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← hc]
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.scalar, Matrix.diagonal, Matrix.smul_apply, mul_comm]
  have hscoord : thetaMatrixCoord (s : Matrix (Fin 2) (Fin 2) ℂ) =
      (ArtinPrimitiveRoots.A1.Spec.horiz (QuotientGroup.mk s),
        ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk s)) := by
    simpa only [thetaMatrixCoords, ArtinPrimitiveRoots.A1.Spec.coordsX] using
      congrFun ((theta_matrix_coordinates_regular (F := F)).2.2 (fun _ => s))
        (Classical.arbitrary (InfinitePlace F))
  have hcoord : thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (ArtinPrimitiveRoots.A1.Spec.horiz (QuotientGroup.mk s),
        ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk s)) := by
    rw [hmatrix, theta_matrix_scalar_invariant _ c.ne_zero]
    exact hscoord
  have hy : 0 < (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2 := by
    rw [hcoord]
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk s)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos _
  let b : SL(2, ℂ) := ArtinPrimitiveRoots.A1.Spec.ptMat
    (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).1
    (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2 hy
  have hpoint : (QuotientGroup.mk b : ArtinPrimitiveRoots.A1.Spec.H3) =
      QuotientGroup.mk s := by
    have hp := ArtinPrimitiveRoots.A1.Spec.pt_horiz_height
      (QuotientGroup.mk s : ArtinPrimitiveRoots.A1.Spec.H3)
    have hx : (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).1 =
        ArtinPrimitiveRoots.A1.Spec.horiz (QuotientGroup.mk s) := congrArg Prod.fst hcoord
    have hh : (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2 =
        ArtinPrimitiveRoots.A1.Spec.height (QuotientGroup.mk s) := congrArg Prod.snd hcoord
    rw [← hx, ← hh] at hp
    simpa only [ArtinPrimitiveRoots.A1.Spec.pt, dif_pos hy] using hp
  have hk : b⁻¹ * s ∈ ArtinPrimitiveRoots.A1.Spec.SU2 := QuotientGroup.eq.mp hpoint
  let k : GL (Fin 2) ℂ := (b⁻¹ * s : SL(2, ℂ))
  refine ⟨hy, k, hk, ?_⟩
  have hsk : (b : GL (Fin 2) ℂ) * k = (s : GL (Fin 2) ℂ) := by
    dsimp [k]
    simp
  change Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk _
  rw [← hsg, ← hsk, map_mul]
  have hb := theta_ptMat_pgl
    (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).1
    (thetaMatrixCoord (g : Matrix (Fin 2) (Fin 2) ℂ)).2 hy
  change Matrix.ProjGenLinGroup.mk (b : GL (Fin 2) ℂ) = _ at hb
  rw [hb, map_mul]
  rfl

end ArtinPrimitiveRoots.Proofs.majorant_sol
