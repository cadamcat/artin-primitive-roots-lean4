import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

noncomputable def pd7dLinearPhase (c : ℂ) (y : ℝ) : ℂ := Complex.exp (c * (y : ℂ))

lemma pd7dLinearPhase_hasDerivAt (c : ℂ) (y : ℝ) :
    HasDerivAt (pd7dLinearPhase c) (c * pd7dLinearPhase c y) y := by
  unfold pd7dLinearPhase
  have hreal : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have harg := hreal.const_mul c
  have hexp := harg.cexp
  simpa only [pd7dLinearPhase, mul_one, mul_comm] using hexp

lemma pd7dLinearPhase_contDiff (c : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pd7dLinearPhase c) := by
  have harg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => c * (y : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact Complex.contDiff_exp.comp harg

lemma pd7dLinearPhase_iteratedDeriv (c : ℂ) (n : ℕ) :
    iteratedDeriv n (pd7dLinearPhase c) = fun y => c ^ n * pd7dLinearPhase c y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [((pd7dLinearPhase_hasDerivAt c y).const_mul (c ^ n)).deriv, pow_succ]
    ring

lemma pd7dLinearPhase_derivative_norm (c : ℂ) (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n (pd7dLinearPhase c) y‖ = ‖c‖ ^ n * ‖pd7dLinearPhase c y‖ := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, pd7dLinearPhase_iteratedDeriv,
    norm_mul, norm_pow]

lemma pd7dLinearPhase_pure_imaginary_norm (a y : ℝ) :
    ‖pd7dLinearPhase (Complex.I * (a : ℂ)) y‖ = 1 := by
  unfold pd7dLinearPhase
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
    zero_sub, sub_zero, add_zero, zero_add, Real.exp_zero]

lemma pd7d_phase_derivative_norm (a y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (pd7dLinearPhase (Complex.I * (a : ℂ))) y‖ = |a| ^ n := by
  rw [pd7dLinearPhase_derivative_norm, pd7dLinearPhase_pure_imaginary_norm, mul_one,
    norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]

end ArtinPrimitiveRoots.TypeII.PD
