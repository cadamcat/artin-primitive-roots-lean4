import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Segment

set_option autoImplicit false

open Set Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- A bounded logarithmic derivative controls a ratio along a complex line segment. -/
theorem norm_ratio_le_exp_of_logDeriv_bound {f : ℂ → ℂ} {z w : ℂ} {M : ℝ}
    (hf : ∀ u ∈ segment ℝ z w, DifferentiableAt ℂ f u)
    (hne : ∀ u ∈ segment ℝ z w, f u ≠ 0)
    (hbound : ∀ u ∈ segment ℝ z w, ‖deriv f u / f u‖ ≤ M) :
    ‖f w / f z‖ ≤ Real.exp (M * ‖w - z‖) := by
  let curve : ℂ → ℂ := fun u => z + u * (w - z)
  let F : ℝ → ℂ := fun t => f (curve t) / f z
  have hfz : f z ≠ 0 := hne z (left_mem_segment ℝ z w)
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      curve t ∈ segment ℝ z w := by
    rw [segment_eq_image' ℝ z w]
    refine ⟨t, ht, ?_⟩
    simp [curve, Complex.real_smul]
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt F (deriv f (curve t) * (w - z) / f z) t := by
    have hcomplex := (hf (curve t) (hmem t ht)).hasDerivAt.comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const (w - z)).const_add z)
    simpa [F, curve, Function.comp_def] using hcomplex.comp_ofReal.div_const (f z)
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hright (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      HasDerivWithinAt F (deriv f (curve t) * (w - z) / f z) (Ici t) t :=
    (hder t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hstart : ‖F 0‖ ≤ (1 : ℝ) := by simp [F, curve, hfz]
  have hdiffbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖deriv f (curve t) * (w - z) / f z‖ ≤
        (M * ‖w - z‖) * ‖F t‖ + 0 := by
    have htu := hmem t ⟨ht.1, ht.2.le⟩
    have hfu : f (curve t) ≠ 0 := hne (curve t) htu
    have heq : deriv f (curve t) * (w - z) / f z =
        (deriv f (curve t) / f (curve t)) * (w - z) * F t := by
      dsimp [F]
      field_simp [hfz, hfu]
    rw [heq, norm_mul, norm_mul, add_zero]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound (curve t) htu) (norm_nonneg _))
      (norm_nonneg _)
  have hend := norm_le_gronwallBound_of_norm_deriv_right_le
    hcont hright hstart hdiffbound 1 (by simp)
  simpa [F, curve, gronwallBound_ε0] using hend

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
