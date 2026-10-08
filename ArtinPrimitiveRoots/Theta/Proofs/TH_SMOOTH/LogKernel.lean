import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Contour
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The inverse-transform integral with the indicated derivative power. -/
def smoothingLogDerivative (C A : ℝ) (r j : ℕ) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, smoothingIntegrand C A r j x ((t : ℂ) * Complex.I)

/-- The smoothing kernel in logarithmic coordinates. -/
def smoothingLogKernel (C A : ℝ) (r : ℕ) : ℝ → ℂ :=
  smoothingLogDerivative C A r 0

private theorem log_derivative_step (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r j : ℕ)
    (x : ℝ) :
    HasDerivAt (smoothingLogDerivative C A r j)
      (smoothingLogDerivative C A r (j + 1) x) x := by
  have hi (n : ℕ) (y : ℝ) : Integrable (fun t : ℝ =>
      smoothingIntegrand C A r n y ((t : ℂ) * Complex.I)) := by
    simpa using (smoothing_quotient_contour C A hC hA r n y).1 0
  obtain ⟨g, _, hgi, _, _, hbound, _⟩ :=
    smoothing_quotient_moments C A hC hA r 0 0 (j + 1)
  have hn (y t : ℝ) :
      ‖smoothingIntegrand C A r (j + 1) y ((t : ℂ) * Complex.I)‖ ≤ g t := by
    have he : (((t : ℂ) * Complex.I) * (y : ℂ)).re = 0 := by simp
    rw [smoothingIntegrand, norm_mul, Complex.norm_exp, he, Real.exp_zero, mul_one]
    simpa using hbound ((t : ℂ) * Complex.I) (by simp) (by simp)
  have hd (t y : ℝ) :
      HasDerivAt (fun v : ℝ => smoothingIntegrand C A r j v ((t : ℂ) * Complex.I))
        (smoothingIntegrand C A r (j + 1) y ((t : ℂ) * Complex.I)) y := by
    let s : ℂ := (t : ℂ) * Complex.I
    have hh := ((((hasDerivAt_id (y : ℂ)).const_mul s).cexp).const_mul
      (s ^ j * smoothingQuotient C A r s)).comp_ofReal
    convert hh using 1
    · rfl
    · dsimp only [smoothingIntegrand, s, id_eq]
      rw [pow_succ]
      ring
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t : ℝ => smoothingIntegrand C A r j y ((t : ℂ) * Complex.I))
    (F' := fun y t : ℝ => smoothingIntegrand C A r (j + 1) y ((t : ℂ) * Complex.I))
    (bound := g) (s := Set.univ) (x₀ := x) Filter.univ_mem
    (Eventually.of_forall fun y => (hi j y).aestronglyMeasurable)
    (hi j x) (hi (j + 1) x).aestronglyMeasurable
    (Eventually.of_forall fun t y _ => hn y t) hgi
    (Eventually.of_forall fun t y _ => hd t y)).2
  exact hder.const_mul ((1 / (2 * Real.pi) : ℝ) : ℂ)

/-- The log kernel is smooth, and every iterated derivative has its absolutely
convergent inverse-transform formula on any vertical line. -/
theorem smoothing_log_kernel_smooth (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (smoothingLogKernel C A r) ∧
      ∀ (j : ℕ) (σ x : ℝ), iteratedDeriv j (smoothingLogKernel C A r) x =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
          smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hiter (j : ℕ) : iteratedDeriv j (smoothingLogKernel C A r) =
      smoothingLogDerivative C A r j := by
    induction j with
    | zero => rw [iteratedDeriv_zero]; rfl
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (log_derivative_step C A hC hA r j x).deriv
  constructor
  · apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    rw [hiter j]
    exact fun x => (log_derivative_step C A hC hA r j x).differentiableAt
  · intro j σ x
    rw [hiter j]
    dsimp only [smoothingLogDerivative]
    congr 1
    simpa using (smoothing_quotient_contour C A hC hA r j x).2 0 σ

end ArtinPrimitiveRoots.Proofs.thsol_smooth
