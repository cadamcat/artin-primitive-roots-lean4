import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».LogDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The real radial profile along a logarithmic dilation. -/
def cubicLogProfile (a x t : ℝ) : ℝ :=
  Real.exp (a * t) * besselK (1 / 3) (x * Real.exp (t / 2))

/-- Polynomial recursion for successive log-scale derivatives. -/
def cubicLogPolynomial (a : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | j + 1 => cubicLogStep a (cubicLogPolynomial a j)

/-- Absolutely convergent integral formula for a log-scale derivative. -/
def cubicLogDerivative (a x : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  Real.exp (a * t) * cubicPolynomialIntegral (cubicLogPolynomial a j)
    (x * Real.exp (t / 2))

/-- Smoothness and bounds for all log-scale derivatives. -/
theorem bessel_cubic_log_control :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (besselK (1 / 3)) (Set.Ioi 0) ∧
      ∀ a : ℝ,
        (∀ x : ℝ, 0 < x →
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cubicLogProfile a x)) ∧
        ∀ j : ℕ, ∃ E F : ℝ, 0 ≤ E ∧ 0 ≤ F ∧
          (∀ x : ℝ, 0 < x → ‖iteratedDeriv j (cubicLogProfile a x) 0‖ ≤
            E * x ^ (-(1 / 3 : ℝ))) ∧
          (∀ x : ℝ, 1 ≤ x → ‖iteratedDeriv j (cubicLogProfile a x) 0‖ ≤
            F * Real.exp (-x / 4)) := by
  have hstep (a x : ℝ) (hx : 0 < x) (j : ℕ) (t : ℝ) :
      HasDerivAt (cubicLogDerivative a x j)
        (cubicLogDerivative a x (j + 1) t) t := by
    change HasDerivAt
      (fun s : ℝ => Real.exp (a * s) * cubicPolynomialIntegral
        (cubicLogPolynomial a j) (x * Real.exp (s / 2)))
      (Real.exp (a * t) * cubicPolynomialIntegral
        (cubicLogStep a (cubicLogPolynomial a j)) (x * Real.exp (t / 2))) t
    exact cubic_polynomial_log_hasDeriv (cubicLogPolynomial a j) a x t hx
  have hformula (a x : ℝ) (hx : 0 < x) (j : ℕ) :
      iteratedDeriv j (cubicLogProfile a x) = cubicLogDerivative a x j := by
    induction j with
    | zero =>
        funext t
        simp only [iteratedDeriv_zero, cubicLogProfile, cubicLogDerivative,
          cubicLogPolynomial, cubicPolynomialIntegral, cubicPolynomialDensity,
          Polynomial.eval_one, one_mul, besselK]
    | succ j ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        exact (hstep a x hx j t).deriv
  have hsmooth (a x : ℝ) (hx : 0 < x) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cubicLogProfile a x) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    rw [hformula a x hx j]
    exact fun t => (hstep a x hx j t).differentiableAt
  constructor
  · have hlog : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => 2 * Real.log x) (Set.Ioi 0) := by
      apply contDiffOn_const.mul
      apply Real.contDiffOn_log.mono
      intro x hx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt hx
    apply ((hsmooth 0 1 (by norm_num)).comp_contDiffOn hlog).congr
    intro x hx
    simp only [Function.comp_apply, cubicLogProfile, zero_mul,
      Real.exp_zero, one_mul]
    rw [show (2 * Real.log x) / 2 = Real.log x by ring, Real.exp_log hx]
  · intro a
    refine ⟨fun x hx => hsmooth a x hx, ?_⟩
    intro j
    obtain ⟨D, E, F, hD, hE, hF, hbound, hint, hsmall, hlarge⟩ :=
      bessel_cubic_polynomial_control (cubicLogPolynomial a j)
    have hzero (x : ℝ) (hx : 0 < x) :
        iteratedDeriv j (cubicLogProfile a x) 0 =
          cubicPolynomialIntegral (cubicLogPolynomial a j) x := by
      rw [hformula a x hx j]
      simp only [cubicLogDerivative, mul_zero, Real.exp_zero, zero_div,
        one_mul, mul_one]
    refine ⟨E, F, hE, hF, ?_, ?_⟩
    · intro x hx
      rw [hzero x hx]
      exact hsmall x hx
    · intro x hx
      rw [hzero x (lt_of_lt_of_le (by norm_num) hx)]
      exact hlarge x hx

end ArtinPrimitiveRoots.Proofs.thsol_smooth
