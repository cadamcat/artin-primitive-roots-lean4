import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Interval
open MeasureTheory intervalIntegral

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- A horizontal simple-pole integral splits into real logarithm and arctangent differences. -/
theorem horizontal_simple_pole_integral (A : ℂ) (a b y : ℝ) (hy : y ≠ 0) :
    (∫ t : ℝ in a..b, A / ((t : ℂ) + (y : ℂ) * Complex.I)) =
      A * ((Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2 : ℝ) : ℂ) -
      A * Complex.I * ((Real.arctan (b / y) - Real.arctan (a / y) : ℝ) : ℂ) := by
  have hsq (t : ℝ) : t ^ 2 + y ^ 2 ≠ 0 := by
    have hpos : 0 < t ^ 2 + y ^ 2 := by
      linarith [sq_nonneg t, sq_pos_iff.mpr hy]
    exact hpos.ne'
  have hdencont : Continuous (fun t : ℝ => t ^ 2 + y ^ 2) :=
    (continuous_id.pow 2).add continuous_const
  have hcont₁ : Continuous (fun t : ℝ => t / (t ^ 2 + y ^ 2)) :=
    continuous_id.div hdencont hsq
  have hcont₂ : Continuous (fun t : ℝ => y / (t ^ 2 + y ^ 2)) :=
    continuous_const.div hdencont hsq
  let L : ℝ → ℝ := fun t => Real.log (t ^ 2 + y ^ 2) / 2
  have hLd (t : ℝ) : HasDerivAt L (t / (t ^ 2 + y ^ 2)) t := by
    have hpow : HasDerivAt (fun u : ℝ => u ^ 2 + y ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const (y ^ 2)
    convert (hpow.log (hsq t)).div_const (2 : ℝ) using 1
    field_simp [hsq t]
    <;> ring
  have hLcont : Continuous (deriv L) := by
    have heq : deriv L = fun t : ℝ => t / (t ^ 2 + y ^ 2) :=
      funext fun t => (hLd t).deriv
    rw [heq]
    exact hcont₁
  have hlogint : (∫ t : ℝ in a..b, t / (t ^ 2 + y ^ 2)) =
      Real.log (b ^ 2 + y ^ 2) / 2 - Real.log (a ^ 2 + y ^ 2) / 2 := by
    calc
      _ = ∫ t : ℝ in a..b, deriv L t :=
        integral_congr fun t _ => (hLd t).deriv.symm
      _ = L b - L a := integral_deriv_eq_sub
        (fun t _ => (hLd t).differentiableAt) (hLcont.intervalIntegrable a b)
      _ = _ := rfl
  let Q : ℝ → ℝ := fun t => Real.arctan (t / y)
  have hQd (t : ℝ) : HasDerivAt Q (y / (t ^ 2 + y ^ 2)) t := by
    have hinner : HasDerivAt (fun u : ℝ => u / y) (1 / y) t :=
      (hasDerivAt_id t).div_const y
    have hOne : 1 + (t / y) ^ 2 ≠ 0 :=
      (show (0 : ℝ) < 1 + (t / y) ^ 2 by positivity).ne'
    convert (Real.hasDerivAt_arctan (t / y)).comp t hinner using 1
    · rfl
    · field_simp [hy, hsq t, hOne]
      <;> ring
  have hQcont : Continuous (deriv Q) := by
    have heq : deriv Q = fun t : ℝ => y / (t ^ 2 + y ^ 2) :=
      funext fun t => (hQd t).deriv
    rw [heq]
    exact hcont₂
  have harctan : (∫ t : ℝ in a..b, y / (t ^ 2 + y ^ 2)) =
      Real.arctan (b / y) - Real.arctan (a / y) := by
    calc
      _ = ∫ t : ℝ in a..b, deriv Q t :=
        integral_congr fun t _ => (hQd t).deriv.symm
      _ = Q b - Q a := integral_deriv_eq_sub
        (fun t _ => (hQd t).differentiableAt) (hQcont.intervalIntegrable a b)
      _ = _ := rfl
  have hinv (t : ℝ) : ((t : ℂ) + (y : ℂ) * Complex.I)⁻¹ =
      ((t : ℂ) - Complex.I * (y : ℂ)) / ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    rw [Complex.inv_def, div_eq_mul_inv]
    congr <;> simp [Complex.conj_ofReal, Complex.normSq] <;> ring
  have heq (t : ℝ) : A / ((t : ℂ) + (y : ℂ) * Complex.I) =
      A * ((t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) -
        A * Complex.I * ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, hinv]
    push_cast
    ring
  have hint₁ : IntervalIntegrable
      (fun t : ℝ => A * ((t / (t ^ 2 + y ^ 2) : ℝ) : ℂ)) volume a b :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hcont₁)).intervalIntegrable a b
  have hint₂ : IntervalIntegrable
      (fun t : ℝ => A * Complex.I * ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ)) volume a b :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hcont₂)).intervalIntegrable a b
  calc
    _ = ∫ t : ℝ in a..b, A * ((t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) -
        A * Complex.I * ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) :=
      integral_congr fun t _ => heq t
    _ = (∫ t : ℝ in a..b, A * ((t / (t ^ 2 + y ^ 2) : ℝ) : ℂ)) -
        (∫ t : ℝ in a..b, A * Complex.I * ((y / (t ^ 2 + y ^ 2) : ℝ) : ℂ)) :=
      integral_sub hint₁ hint₂
    _ = A * ((∫ t : ℝ in a..b, t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) -
        A * Complex.I * ((∫ t : ℝ in a..b, y / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    _ = _ := by rw [hlogint, harctan]

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
