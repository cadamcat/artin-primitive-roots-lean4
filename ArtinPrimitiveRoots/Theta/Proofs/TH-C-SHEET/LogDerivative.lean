import ArtinPrimitiveRoots.Theta.Proofs.«TH-C-SHEET».PolynomialControl
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The polynomial produced by differentiating the weighted log-scale density. -/
def cubicLogStep (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C a * P + Polynomial.C (1 / 2) * Polynomial.X * (P.derivative - P)

/-- Differentiation under the cosh integral in log-scale coordinates. -/
theorem cubic_polynomial_log_hasDeriv (P : Polynomial ℝ) (a x t : ℝ) (hx : 0 < x) :
    HasDerivAt
      (fun s : ℝ => Real.exp (a * s) * cubicPolynomialIntegral P (x * Real.exp (s / 2)))
      (Real.exp (a * t) * cubicPolynomialIntegral (cubicLogStep a P)
        (x * Real.exp (t / 2))) t := by
  let Q := cubicLogStep a P
  let Y : ℝ → ℝ := fun s => x * Real.exp (s / 2)
  let W : ℝ → ℝ → ℝ := fun s u =>
    Real.exp (a * s) * cubicPolynomialDensity P (Y s) u
  let W' : ℝ → ℝ → ℝ := fun s u =>
    Real.exp (a * s) * cubicPolynomialDensity Q (Y s) u
  let β : ℝ := x * Real.exp ((t - 1) / 2)
  let G : ℝ := Real.exp (|a| * (|t| + 1))
  obtain ⟨D, E, F, hD, hE, hF, hQbound, hQint, hQsmall, hQlarge⟩ :=
    bessel_cubic_polynomial_control Q
  let bound : ℝ → ℝ := fun u => (G * D) *
    (Real.exp (-(β / 2) * Real.cosh u) * Real.cosh ((1 / 3 : ℝ) * u))
  have hY (s : ℝ) : 0 < Y s := mul_pos hx (Real.exp_pos _)
  have hβ : 0 < β := mul_pos hx (Real.exp_pos _)
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hInt (R : Polynomial ℝ) (s : ℝ) :
      IntegrableOn (fun u => Real.exp (a * s) * cubicPolynomialDensity R (Y s) u)
        (Set.Ioi 0) := by
    obtain ⟨_, _, _, _, _, _, _, hi, _, _⟩ := bessel_cubic_polynomial_control R
    exact (hi (Y s) (hY s)).const_mul _
  have hball (s : ℝ) (hs : s ∈ Metric.ball t 1) :
      t - 1 ≤ s ∧ |s| ≤ |t| + 1 := by
    have hd : |s - t| < 1 := by
      simpa only [Real.dist_eq] using Metric.mem_ball.mp hs
    constructor
    · have hl := (abs_lt.mp hd).1
      linarith
    · calc
        |s| = |(s - t) + t| := by congr 1; ring
        _ ≤ |s - t| + |t| := by
          simpa only [Real.norm_eq_abs] using norm_add_le (s - t) t
        _ ≤ |t| + 1 := by linarith
  have hYs (s : ℝ) (hs : s ∈ Metric.ball t 1) : β ≤ Y s := by
    apply mul_le_mul_of_nonneg_left _ hx.le
    apply Real.exp_le_exp.mpr
    linarith [(hball s hs).1]
  have hweight (s : ℝ) (hs : s ∈ Metric.ball t 1) :
      Real.exp (a * s) ≤ G := by
    apply Real.exp_le_exp.mpr
    calc
      a * s ≤ |a * s| := le_abs_self _
      _ = |a| * |s| := abs_mul _ _
      _ ≤ |a| * (|t| + 1) :=
        mul_le_mul_of_nonneg_left (hball s hs).2 (abs_nonneg _)
  have hbound (s : ℝ) (hs : s ∈ Metric.ball t 1) (u : ℝ) :
      ‖W' s u‖ ≤ bound u := by
    let q : ℝ := Y s * Real.cosh u
    have hq : 0 ≤ q := (mul_pos (hY s) (Real.cosh_pos u)).le
    have hd : Real.exp (-q / 2) ≤ Real.exp (-(β / 2) * Real.cosh u) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (hYs s hs) (Real.cosh_pos u).le
      dsimp only [q]
      nlinarith
    calc
      ‖W' s u‖ = (Real.exp (a * s) *
          (‖Q.eval q‖ * Real.exp (-q))) * Real.cosh ((1 / 3 : ℝ) * u) := by
        simp only [W', cubicPolynomialDensity, q, norm_mul,
          Real.norm_of_nonneg (Real.exp_pos _).le,
          Real.norm_of_nonneg (Real.cosh_pos _).le, neg_mul, mul_assoc]
      _ ≤ (Real.exp (a * s) * (D * Real.exp (-q / 2))) *
          Real.cosh ((1 / 3 : ℝ) * u) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hQbound q hq) (Real.exp_pos _).le)
          (Real.cosh_pos _).le
      _ ≤ (G * (D * Real.exp (-(β / 2) * Real.cosh u))) *
          Real.cosh ((1 / 3 : ℝ) * u) := by
        apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
        exact mul_le_mul (hweight s hs) (mul_le_mul_of_nonneg_left hd hD)
          (mul_nonneg hD (Real.exp_pos _).le) hG
      _ = bound u := by dsimp only [bound]; ring
  have hbi : IntegrableOn bound (Set.Ioi 0) := by
    obtain ⟨B, hB, hi⟩ := bessel_cubic_cosh_control
    exact (hi (β / 2) (by positivity)).1.const_mul (G * D)
  have hpoint (u s : ℝ) : HasDerivAt (fun r => W r u) (W' s u) s := by
    have hq : HasDerivAt (fun r : ℝ => Y r * Real.cosh u)
        ((Y s * Real.cosh u) / 2) s := by
      have hh := ((((hasDerivAt_id s).div_const 2).exp).const_mul x).mul_const
        (Real.cosh u)
      convert hh using 1
      · rfl
      · dsimp only [Y, id_eq]
        ring
    have hw : HasDerivAt (fun r : ℝ => Real.exp (a * r))
        (a * Real.exp (a * s)) s := by
      convert ((hasDerivAt_id s).const_mul a).exp using 1 <;>
        simp only [id_eq, mul_one] <;> ring
    have hh := (((hw.mul ((P.hasDerivAt (Y s * Real.cosh u)).comp s hq)).mul
      hq.neg.exp).mul_const (Real.cosh ((1 / 3 : ℝ) * u)))
    convert hh using 1
    · funext r
      dsimp only [W, cubicPolynomialDensity]
      simp only [neg_mul, Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
      ring
    · dsimp only [W', Q, cubicPolynomialDensity, cubicLogStep]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_sub, neg_mul,
        Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
      ring
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := W) (F' := W') (bound := bound) (s := Metric.ball t 1) (x₀ := t)
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (Metric.ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall fun s => (hInt P s).aestronglyMeasurable)
    (hInt P t) (hInt Q t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u s hs => hbound s hs u) hbi
    (Filter.Eventually.of_forall fun u s _ => hpoint u s)).2
  convert hd using 1
  · funext s
    dsimp only [W, cubicPolynomialIntegral, Y]
    rw [integral_const_mul]
  · dsimp only [W', Q, cubicPolynomialIntegral, Y]
    rw [integral_const_mul]


end ArtinPrimitiveRoots.Proofs.thsol_smooth
