import OAI.NumberTheory.DirichletL.ContinuationContour

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rows_sol

/-- The Gaussian simple-pole correction vanishes on the horizontal sides of
an expanding rectangle, including when the real pole lies in the strip. -/
theorem gaussian_pole_horizontal_vanish (a b p : ℝ) (hab : a ≤ b) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      Complex.exp ((((x : ℂ) + (-T) * Complex.I) - p) ^ 2) /
        (((x : ℂ) + (-T) * Complex.I) - p)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      Complex.exp ((((x : ℂ) + T * Complex.I) - p) ^ 2) /
        (((x : ℂ) + T * Complex.I) - p)) atTop (𝓝 0) := by
  let B : ℝ := max |a - p| |b - p|
  have hB : 0 ≤ B := (abs_nonneg (a - p)).trans (le_max_left _ _)
  have hsq (x : ℝ) (hx : x ∈ Icc a b) : (x - p) ^ 2 ≤ B ^ 2 := by
    have ha : |a - p| ≤ B := le_max_left _ _
    have hb : |b - p| ≤ B := le_max_right _ _
    have hax := neg_abs_le (a - p)
    have hbx := le_abs_self (b - p)
    have hxabs : |x - p| ≤ B := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    nlinarith [sq_abs (x - p), abs_nonneg (x - p)]
  have hbound (x t : ℝ) (hx : x ∈ Icc a b) (ht : 1 ≤ |t|) :
      ‖Complex.exp ((((x : ℂ) + t * Complex.I) - p) ^ 2) /
        (((x : ℂ) + t * Complex.I) - p)‖ ≤
          Real.exp (B ^ 2) * Real.exp (-(t ^ 2)) := by
    let z : ℂ := ((x : ℂ) + t * Complex.I) - p
    have hzre : z.re = x - p := by simp [z]
    have hzim : z.im = t := by simp [z]
    have hzsq : (z ^ 2).re = (x - p) ^ 2 - t ^ 2 := by
      rw [pow_two, Complex.mul_re, hzre, hzim]
      ring
    have hden : 1 ≤ ‖z‖ := ht.trans (by simpa [hzim] using Complex.abs_im_le_norm z)
    change ‖Complex.exp (z ^ 2) / z‖ ≤ _
    rw [norm_div, Complex.norm_exp, hzsq]
    calc
      _ ≤ Real.exp ((x - p) ^ 2 - t ^ 2) / 1 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hden
      _ ≤ Real.exp (B ^ 2 - t ^ 2) := by
        simp only [div_one]
        exact Real.exp_le_exp.mpr (sub_le_sub_right (hsq x hx) _)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by decide)))
  have hlim : Tendsto
      (fun T : ℝ => Real.exp (B ^ 2) * Real.exp (-(T ^ 2)) * |b - a|)
      atTop (𝓝 0) := by
    simpa using (hexp.const_mul (Real.exp (B ^ 2))).mul_const |b - a|
  have htail (T : ℝ) (hT : 1 ≤ T) (t : ℝ) (ht : |t| = T) :
      ‖∫ x : ℝ in a..b,
        Complex.exp ((((x : ℂ) + t * Complex.I) - p) ^ 2) /
          (((x : ℂ) + t * Complex.I) - p)‖ ≤
            Real.exp (B ^ 2) * Real.exp (-(T ^ 2)) * |b - a| := by
    have ht2 : t ^ 2 = T ^ 2 := by rw [← ht, sq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc a b := by
      simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx
    simpa [ht2] using hbound x t hx' (by rwa [ht])
  constructor <;> apply tendsto_zero_iff_norm_tendsto_zero.mpr
  · apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [Complex.ofReal_neg] using
      htail T hT (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)])
  · apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact htail T hT T (abs_of_nonneg (by linarith))

end ArtinPrimitiveRoots.Proofs.a2_rows_sol
