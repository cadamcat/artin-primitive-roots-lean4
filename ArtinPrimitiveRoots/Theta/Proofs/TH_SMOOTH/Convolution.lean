import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.MellinKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem mellin_denominator_ne_zero (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (r : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    (C : ℂ) * (A : ℂ) ^ s *
      (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hC.ne')
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne')))
  · apply pow_ne_zero
    apply mul_ne_zero
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num [Complex.add_re]
      linarith
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num [Complex.add_re]
      linarith

private theorem log_profile_integrable (V : ℝ → ℂ) (h0 : mellin V 0 ≠ 0) :
    Integrable (fun x : ℝ => V (Real.exp x)) := by
  have hi : MellinConvergent V 0 := Integrable.of_integral_ne_zero h0
  have hh := (integrable_comp_exp (fun T : ℝ => (T : ℂ) ^ ((0 : ℂ) - 1) • V T)).2 hi
  convert hh using 1
  funext x
  simp only [zero_sub, Complex.cpow_neg_one, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)), one_mul]

private theorem log_mellin (V : ℝ → ℂ) (s : ℂ) :
    mellin V s = ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * V (Real.exp x) := by
  rw [mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_nonneg x), Real.log_exp,
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem gaussian_inverse_integral (x : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      Complex.exp (-(t : ℂ) ^ 2) * Complex.exp ((-t * x : ℝ) * Complex.I) =
        (((2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2 / 4) : ℝ) : ℂ) := by
  have heq : (∫ t : ℝ, Complex.exp (-(t : ℂ) ^ 2) *
      Complex.exp ((-t * x : ℝ) * Complex.I)) =
      ∫ t : ℝ, Complex.exp (Complex.I * -(x : ℂ) * (t : ℂ)) *
        Complex.exp (-(t : ℂ) ^ 2) := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hg := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (-(x : ℂ))
  simp only [neg_one_mul, div_one, mul_one, neg_sq] at hg
  rw [heq, hg]
  have hsqrt : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [hsqrt]
  have hexp : Complex.exp (-(x : ℂ) ^ 2 / 4) = (Real.exp (-x ^ 2 / 4) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [hexp]
  norm_cast
  rw [← mul_assoc]
  congr 1
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr Real.pi_pos).ne']
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

/-- A profile with the prescribed theta Mellin transform convolves with the
actual smoothing kernel to the logarithmic Gaussian at every positive point. -/
theorem smoothing_kernel_convolution (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (r : ℕ) (V : ℝ → ℂ)
    (hM : ∀ s : ℂ, -(5 / 6 : ℝ) < s.re → mellin V s =
      (C : ℂ) * (A : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r)
    (u : ℝ) (hu : 0 < u) :
    ∫ T in Set.Ioi (0 : ℝ), smoothingKernel C A r T * V (u * T) / T =
      (((2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log u) ^ 2 / 4) : ℝ) : ℂ) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let Q (τ : ℝ) : ℂ := smoothingQuotient C A r ((τ : ℂ) * Complex.I)
  let W (t : ℝ) : ℂ := V (u * Real.exp t)
  let f (t τ : ℝ) : ℂ := Q τ * Complex.exp ((τ : ℂ) * Complex.I * (t : ℂ)) * W t
  have h0 : mellin V 0 ≠ 0 := by
    rw [hM 0 (by norm_num)]
    exact mellin_denominator_ne_zero C A hC hA r 0 (by norm_num)
  have hV := log_profile_integrable V h0
  have hW : Integrable W := by
    simpa only [Real.exp_add, Real.exp_log hu] using hV.comp_add_left (Real.log u)
  have hQ : Integrable Q := by
    obtain ⟨_, _, _, _, _, _, hi⟩ := smoothing_quotient_moments C A hC hA r 0 0 0
    simpa using hi 0 le_rfl le_rfl
  have hphase : Continuous (fun z : ℝ × ℝ =>
      Complex.exp ((z.2 : ℂ) * Complex.I * (z.1 : ℂ))) := by fun_prop
  have hfmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1 z.2)
      (volume.prod volume) :=
    (hQ.aestronglyMeasurable.comp_snd.mul hphase.aestronglyMeasurable).mul
      hW.aestronglyMeasurable.comp_fst
  have hnorm (t τ : ℝ) : ‖Complex.exp ((τ : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hf : Integrable (fun z : ℝ × ℝ => f z.1 z.2) (volume.prod volume) := by
    apply (hW.norm.mul_prod hQ.norm).mono' hfmeas
    filter_upwards [] with z
    simp only [f, norm_mul, hnorm, mul_one]
    exact le_of_eq (mul_comm _ _)
  have hinner (τ : ℝ) : ∫ t : ℝ, Complex.exp ((τ : ℂ) * Complex.I * (t : ℂ)) * W t =
      Complex.exp (-((τ : ℂ) * Complex.I) * (Real.log u : ℂ)) *
        mellin V ((τ : ℂ) * Complex.I) := by
    let s : ℂ := (τ : ℂ) * Complex.I
    have hp (t : ℝ) : Complex.exp (s * (t : ℂ)) * W t =
        Complex.exp (-s * (Real.log u : ℂ)) *
          (Complex.exp (s * ((Real.log u + t : ℝ) : ℂ)) * V (Real.exp (Real.log u + t))) := by
      rw [Real.exp_add, Real.exp_log hu]
      dsimp only [W]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    calc
      (∫ t : ℝ, Complex.exp (s * (t : ℂ)) * W t) =
          Complex.exp (-s * (Real.log u : ℂ)) *
            ∫ t : ℝ, Complex.exp (s * ((Real.log u + t : ℝ) : ℂ)) *
              V (Real.exp (Real.log u + t)) := by
        simp_rw [hp]
        rw [integral_const_mul]
      _ = Complex.exp (-s * (Real.log u : ℂ)) * mellin V s := by
        rw [integral_add_left_eq_self
          (fun t : ℝ => Complex.exp (s * (t : ℂ)) * V (Real.exp t)) (Real.log u), log_mellin]
  have hproduct (τ : ℝ) : Q τ * mellin V ((τ : ℂ) * Complex.I) =
      Complex.exp (-(τ : ℂ) ^ 2) := by
    have hs : -(5 / 6 : ℝ) < ((τ : ℂ) * Complex.I).re := by norm_num
    dsimp only [Q]
    rw [(smoothing_quotient_control C A hC hA r).2.1,
      hM _ hs, div_mul_cancel₀ _ (mellin_denominator_ne_zero C A hC hA r _ hs)]
    rw [mul_pow, Complex.I_sq, mul_neg_one]
  calc
    (∫ T in Set.Ioi (0 : ℝ), smoothingKernel C A r T * V (u * T) / T) =
        ∫ t : ℝ, smoothingLogKernel C A r t * W t := by
      rw [← integral_comp_exp]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [smoothingKernel, ite_eq_left (Real.exp_pos t), Real.log_exp]
      simp only [Complex.real_smul, W]
      field_simp
    _ = c * ∫ t : ℝ, ∫ τ : ℝ, f t τ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [smoothingLogKernel, smoothingLogDerivative, smoothingIntegrand,
        pow_zero, one_mul, f, Q]
      rw [integral_mul_const]
      ring
    _ = c * ∫ τ : ℝ, ∫ t : ℝ, f t τ := by
      rw [integral_integral_swap hf]
    _ = c * ∫ τ : ℝ, Complex.exp (-(τ : ℂ) ^ 2) *
        Complex.exp ((-τ * Real.log u : ℝ) * Complex.I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with τ
      have hh : (∫ t : ℝ, f t τ) = Q τ *
          ∫ t : ℝ, Complex.exp ((τ : ℂ) * Complex.I * (t : ℂ)) * W t := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        exact mul_assoc _ _ _
      rw [hh, hinner, ← mul_assoc, mul_right_comm, hproduct]
      congr 2
      push_cast
      ring
    _ = _ := gaussian_inverse_integral (Real.log u)

end ArtinPrimitiveRoots.Proofs.thsol_smooth
