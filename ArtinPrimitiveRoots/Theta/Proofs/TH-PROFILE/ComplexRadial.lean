import ArtinPrimitiveRoots.A1.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

open ArtinPrimitiveRoots.A1

/-- Radial derivatives preserve real smoothness on the punctured complex plane. -/
theorem complex_normDeriv_contDiff (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {y | y ≠ 0}) (j : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (normDeriv j f) {y | y ≠ 0} := by
  have hU : IsOpen {y : ℂ | y ≠ 0} := isOpen_ne
  induction j generalizing f with
  | zero =>
    apply hf.congr
    intro y hy
    simp only [normDeriv, iteratedDeriv_zero, zero_div, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  | succ j ih =>
    let g : ℂ → ℂ := fun y => fderiv ℝ f y (y / 2)
    have hdf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) {y | y ≠ 0} :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf).2
    have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℂ => y / 2) :=
      contDiff_id.div_const (2 : ℂ)
    have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g {y | y ≠ 0} :=
      hdf.clm_apply hv.contDiffOn
    have hEq (y : ℂ) (hy : y ≠ 0) : normDeriv (j + 1) f y = normDeriv j g y := by
      have hcurvederiv : deriv (fun t : ℝ => f ((Real.exp (t / 2) : ℂ) * y)) =
          fun t : ℝ => g ((Real.exp (t / 2) : ℂ) * y) := by
        funext t
        have hinput : HasDerivAt (fun s : ℝ => (Real.exp (s / 2) : ℂ) * y)
            (((Real.exp (t / 2) : ℂ) * y) / 2) t := by
          have hr : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) / 2) t := by
            simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using!
              (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)
          simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, div_mul_eq_mul_div] using!
            hr.ofReal_comp.mul_const y
        have hz : (Real.exp (t / 2) : ℂ) * y ≠ 0 :=
          mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hy
        have hdiff : DifferentiableAt ℝ f ((Real.exp (t / 2) : ℂ) * y) :=
          (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
        exact (hdiff.hasFDerivAt.comp_hasDerivAt t hinput).deriv
      change iteratedDeriv (j + 1) (fun t : ℝ => f ((Real.exp (t / 2) : ℂ) * y)) 0 =
        iteratedDeriv j (fun t : ℝ => g ((Real.exp (t / 2) : ℂ) * y)) 0
      rw [iteratedDeriv_succ', hcurvederiv]
    exact (ih g hg).congr hEq

end ArtinPrimitiveRoots.Proofs.thsol_sheets
