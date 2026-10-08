import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.PositiveKernel
import Mathlib.Analysis.MellinInversion

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem weighted_log_kernel_integrable (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (r : ℕ) (σ : ℝ) :
    Integrable (fun x : ℝ => (Real.exp (σ * x) : ℂ) *
      smoothingLogKernel C A r (-x)) := by
  have hi : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
      intro x hx
      dsimp only
      rw [abs_of_nonpos (show x ≤ 0 from hx), neg_neg]
    · apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_nonneg (show 0 ≤ x from le_of_lt hx)]
  obtain ⟨B, hBpos, hB⟩ := smoothing_log_kernel_decay C A hC hA r (|σ| + 1) 0
  simp only [iteratedDeriv_zero, abs_of_pos (by positivity : 0 < |σ| + 1)] at hB
  have hc : Continuous (fun x : ℝ => (Real.exp (σ * x) : ℂ) *
      smoothingLogKernel C A r (-x)) := by
    apply Continuous.mul
    · fun_prop
    · exact (smoothing_log_kernel_smooth C A hC hA r).1.continuous.comp continuous_neg
  apply (hi.const_mul B).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  have hsx : σ * x ≤ |σ| * |x| := by
    calc
      σ * x ≤ |σ * x| := le_abs_self _
      _ = |σ| * |x| := abs_mul _ _
  calc
    ‖(Real.exp (σ * x) : ℂ) * smoothingLogKernel C A r (-x)‖ =
        Real.exp (σ * x) * ‖smoothingLogKernel C A r (-x)‖ := by
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (σ * x) * (B * Real.exp (-(|σ| + 1) * |x|)) :=
      mul_le_mul_of_nonneg_left (by simpa only [abs_neg] using hB (-x)) (Real.exp_nonneg _)
    _ = B * Real.exp (σ * x - (|σ| + 1) * |x|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ B * Real.exp (-|x|) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hBpos
      nlinarith

private theorem weighted_log_kernel_eq_fourier (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (r : ℕ) (σ : ℝ) (x : ℝ) :
    (Real.exp (σ * x) : ℂ) * smoothingLogKernel C A r (-x) =
      𝓕 (fun t : ℝ => smoothingQuotient C A r
        ((σ : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I)) x := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let f (t : ℝ) : ℂ := smoothingQuotient C A r ((σ : ℂ) + (t : ℂ) * Complex.I) *
    Complex.exp ((-t * x : ℝ) * Complex.I)
  have hline := (smoothing_log_kernel_smooth C A hC hA r).2 0 σ (-x)
  rw [iteratedDeriv_zero] at hline
  have hpoint (t : ℝ) : (Real.exp (σ * x) : ℂ) *
      smoothingIntegrand C A r 0 (-x) ((σ : ℂ) + (t : ℂ) * Complex.I) = f t := by
    dsimp only [smoothingIntegrand, f]
    rw [pow_zero, one_mul, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc
    (Real.exp (σ * x) : ℂ) * smoothingLogKernel C A r (-x) = c * ∫ t : ℝ, f t := by
      rw [hline, mul_left_comm, ← integral_const_mul]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ t : ℝ, f ((2 * Real.pi) * t) := by
      rw [Measure.integral_comp_mul_left]
      rw [abs_of_pos (show 0 < (2 * Real.pi)⁻¹ by positivity)]
      simp only [Complex.real_smul, one_div, c]
    _ = 𝓕 (fun t : ℝ => smoothingQuotient C A r
        ((σ : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I)) x := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp only [f, smul_eq_mul]
      rw [mul_comm]
      congr 2
      push_cast
      ring

private theorem smoothing_kernel_mellin_convergent (C A : ℝ)
    (hC : 0 < C) (hA : 0 < A) (r : ℕ) (s : ℂ) :
    MellinConvergent (smoothingKernel C A r) (-s) := by
  have hi : Integrable (fun x : ℝ => (Real.exp (-s.re * x) : ℂ) *
      smoothingLogKernel C A r x) := by
    simpa only [neg_one_mul, neg_neg, mul_neg, neg_mul, one_mul] using
      (weighted_log_kernel_integrable C A hC hA r s.re).comp_mul_left'
        (by norm_num : (-1 : ℝ) ≠ 0)
  have hc : Continuous (fun x : ℝ => Complex.exp (-s * (x : ℂ)) *
      smoothingLogKernel C A r x) := by
    apply Continuous.mul
    · fun_prop
    · exact (smoothing_log_kernel_smooth C A hC hA r).1.continuous
  have hce : Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) *
      smoothingLogKernel C A r x) := by
    apply hi.mono hc.aestronglyMeasurable
    filter_upwards [] with x
    simp [Complex.norm_exp]
  rw [MellinConvergent, ← integrable_comp_exp]
  convert hce using 1
  funext x
  rw [smoothingKernel, ite_eq_left (Real.exp_pos x), Real.log_exp]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_nonneg x), Real.log_exp,
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The actual smoothing kernel has an absolutely convergent Mellin transform
on every vertical line, equal to the entire smoothing quotient. -/
theorem smoothing_kernel_hasMellin (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (r : ℕ) (s : ℂ) :
    HasMellin (smoothingKernel C A r) (-s) (smoothingQuotient C A r s) := by
  refine ⟨smoothing_kernel_mellin_convergent C A hC hA r s, ?_⟩
  let q (t : ℝ) : ℂ := smoothingQuotient C A r
    ((s.re : ℂ) + (2 * Real.pi * t : ℝ) * Complex.I)
  have hq : Integrable q := by
    obtain ⟨_, _, _, _, _, _, hi⟩ := smoothing_quotient_moments C A hC hA r s.re s.re 0
    have hh := hi s.re le_rfl le_rfl
    simp only [pow_zero, one_mul] at hh
    exact hh.comp_mul_left' (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  have hqcont : Continuous q := by
    apply (smoothing_quotient_control C A hC hA r).1.continuous.comp
    fun_prop
  have heq : (fun x : ℝ => (Real.exp (s.re * x) : ℂ) *
      smoothingLogKernel C A r (-x)) = 𝓕 q := by
    funext x
    exact weighted_log_kernel_eq_fourier C A hC hA r s.re x
  have hFq : Integrable (𝓕 q) := heq ▸ weighted_log_kernel_integrable C A hC hA r s.re
  calc
    mellin (smoothingKernel C A r) (-s) = 𝓕 (𝓕 q) (-(s.im / (2 * Real.pi))) := by
      rw [mellin_eq_fourier]
      simp only [Complex.neg_re, Complex.neg_im, neg_neg, neg_div,
        smoothingKernel, Real.exp_pos, ite_true, Real.log_exp, Complex.real_smul]
      rw [heq]
    _ = 𝓕⁻ (𝓕 q) (s.im / (2 * Real.pi)) :=
      (Real.fourierInv_eq_fourier_neg _ _).symm
    _ = q (s.im / (2 * Real.pi)) := hq.fourierInv_fourier_eq hFq hqcont.continuousAt
    _ = smoothingQuotient C A r s := by
      dsimp only [q]
      rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))]
      rw [Complex.re_add_im]

end ArtinPrimitiveRoots.Proofs.thsol_smooth
