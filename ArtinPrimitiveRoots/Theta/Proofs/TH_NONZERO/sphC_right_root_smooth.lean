import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

private theorem bottom_row_norm_pos (g : GL (Fin 2) ℂ) :
    0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · have hd : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      intro hd
      apply g.det_ne_zero
      simp [Matrix.det_fin_two, hc, hd]
    positivity
  · positivity

private theorem spherical_right_root_formula (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) :
    sphC s (QuotientGroup.mk g * nC z) =
      (↑(‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
          ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z +
            (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)) : ℂ) ^ (1 + 2 * s) := by
  have hq : QuotientGroup.mk g * nC z = QuotientGroup.mk (g * upperM ℂ z) := by
    change QuotientGroup.mk g * QuotientGroup.mk (upperM ℂ z) = _
    simp only [QuotientGroup.mk_mul]
  rw [hq, sphC_mk, sphericalC]
  have hdet : ‖Matrix.det ((g * upperM ℂ z : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)‖ = ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
    change ‖((Matrix.GeneralLinearGroup.det (g * upperM ℂ z) : ℂˣ) : ℂ)‖ = _
    rw [map_mul]
    simp [upperM]
  have hrow :
      ‖((g * upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖((g * upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
    simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hdet, hrow]

/-- The spherical section is smooth along every right upper-root orbit. -/
theorem sphC_right_root_smooth (s : ℂ) (g : PGL2 ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => sphC s (g * nC z)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  let c : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let d : ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  let N : ℝ := ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖
  let den : ℂ → ℝ := fun z => ‖c‖ ^ 2 + ‖c * z + d‖ ^ 2
  let ratio : ℂ → ℝ := fun z => N / den z
  have hdenpos (z : ℂ) : 0 < den z := by
    simpa [den, c, d, upperM, Matrix.mul_apply, Fin.sum_univ_two] using
      bottom_row_norm_pos (g * upperM ℂ z)
  have hNpos : 0 < N := norm_pos_iff.mpr g.det_ne_zero
  have hratioPos (z : ℂ) : 0 < ratio z := div_pos hNpos (hdenpos z)
  have haff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => c * z + d) := by
    fun_prop
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) den :=
    contDiff_const.add ((contDiff_norm_sq ℂ).comp haff)
  have hratio : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ratio :=
    contDiff_const.div hden (fun z => ne_of_gt (hdenpos z))
  have hlog : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (Real.log (ratio z) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp (hratio.log (fun z => ne_of_gt (hratioPos z)))
  have heq : (fun z : ℂ => sphC s (QuotientGroup.mk g * nC z)) =
      fun z => Complex.exp ((Real.log (ratio z) : ℂ) * (1 + 2 * s)) := by
    funext z
    rw [spherical_right_root_formula]
    change (ratio z : ℂ) ^ (1 + 2 * s) = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (hratioPos z))), ← Complex.ofReal_log (le_of_lt (hratioPos z))]
  rw [heq]
  exact (hlog.mul contDiff_const).cexp

end ArtinPrimitiveRoots.A1.Theta
