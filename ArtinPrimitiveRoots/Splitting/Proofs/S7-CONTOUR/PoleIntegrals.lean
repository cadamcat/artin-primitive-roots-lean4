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

/-- A vertical simple-pole integral is the rotated horizontal formula. -/
theorem vertical_simple_pole_integral (A : ℂ) (a b x : ℝ) (hx : x ≠ 0) :
    (∫ t : ℝ in a..b, A / ((x : ℂ) + (t : ℂ) * Complex.I)) =
      (A / Complex.I) * ((Real.log (b ^ 2 + x ^ 2) / 2 -
        Real.log (a ^ 2 + x ^ 2) / 2 : ℝ) : ℂ) -
      (A / Complex.I) * Complex.I *
        ((Real.arctan (b / (-x)) - Real.arctan (a / (-x)) : ℝ) : ℂ) := by
  have heq (t : ℝ) : A / ((x : ℂ) + (t : ℂ) * Complex.I) =
      (A / Complex.I) / ((t : ℂ) + (-x : ℝ) * Complex.I) := by
    rw [div_div]
    congr 1
    push_cast
    ring_nf
    <;> simp [Complex.I_sq]
  calc
    _ = ∫ t : ℝ in a..b, (A / Complex.I) /
        ((t : ℂ) + (-x : ℝ) * Complex.I) :=
      integral_congr fun t _ => heq t
    _ = _ := by
      simpa only [neg_sq] using
        horizontal_simple_pole_integral (A / Complex.I) a b (-x) (neg_ne_zero.mpr hx)

/-- The counterclockwise rectangle integral of a simple pole surrounding zero. -/
theorem rectangle_simple_pole_integral (A : ℂ) (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    (∫ t : ℝ in a..b, A / ((t : ℂ) + (c : ℂ) * Complex.I)) -
      (∫ t : ℝ in a..b, A / ((t : ℂ) + (d : ℂ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in c..d, A / ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in c..d, A / ((a : ℂ) + (t : ℂ) * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I * A := by
  rw [horizontal_simple_pole_integral A a b c hc.ne,
    horizontal_simple_pole_integral A a b d hd.ne',
    vertical_simple_pole_integral A c d b hb.ne',
    vertical_simple_pole_integral A c d a ha.ne]
  have hrec₁ := Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha hc)
  have hrec₂ := Real.arctan_inv_of_pos (div_pos hb hd)
  have hrec₃ := Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hb hc)
  have hrec₄ := Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hd)
  rw [inv_div] at hrec₁ hrec₂ hrec₃ hrec₄
  have hAI : A / Complex.I = -(A * Complex.I) := by
    simp [div_eq_mul_inv, Complex.inv_I]
  simp only [hAI, div_neg, Real.arctan_neg]
  rw [hrec₁, hrec₂, hrec₃, hrec₄]
  rw [add_comm (d ^ 2) (b ^ 2), add_comm (c ^ 2) (b ^ 2),
    add_comm (d ^ 2) (a ^ 2), add_comm (c ^ 2) (a ^ 2)]
  push_cast
  ring_nf
  <;> simp [Complex.I_sq]
  <;> ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
