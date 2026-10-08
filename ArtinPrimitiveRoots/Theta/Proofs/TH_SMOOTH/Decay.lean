import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.LogKernel

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem log_kernel_line_bound (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r j : ℕ)
    (σ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ‖iteratedDeriv j (smoothingLogKernel C A r) x‖ ≤ B * Real.exp (σ * x) := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let W (t : ℝ) : ℂ := ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j *
    smoothingQuotient C A r ((σ : ℂ) + (t : ℂ) * Complex.I)
  let B : ℝ := ‖c‖ * ∫ t : ℝ, ‖W t‖
  refine ⟨B, mul_nonneg (norm_nonneg _) (integral_nonneg fun t => norm_nonneg _), ?_⟩
  intro x
  have hn (t : ℝ) :
      ‖smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
        ‖W t‖ * Real.exp (σ * x) := by
    have he : (((σ : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)).re = σ * x := by simp
    rw [smoothingIntegrand, norm_mul, Complex.norm_exp, he]
  calc
    ‖iteratedDeriv j (smoothingLogKernel C A r) x‖ = ‖c‖ *
        ‖∫ t : ℝ, smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [(smoothing_log_kernel_smooth C A hC hA r).2 j σ x, norm_mul]
    _ ≤ ‖c‖ * ∫ t : ℝ,
        ‖smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = B * Real.exp (σ * x) := by
      simp_rw [hn]
      rw [integral_mul_const]
      dsimp only [B]
      ring

/-- Every log derivative of the smoothing kernel decays faster than any fixed
exponential at both ends of the real log coordinate. -/
theorem smoothing_log_kernel_decay (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r : ℕ)
    (N : ℝ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ‖iteratedDeriv j (smoothingLogKernel C A r) x‖ ≤
        B * Real.exp (-|N| * |x|) := by
  obtain ⟨Bplus, hBplus, hplus⟩ := log_kernel_line_bound C A hC hA r j |N|
  obtain ⟨Bminus, _, hminus⟩ := log_kernel_line_bound C A hC hA r j (-|N|)
  refine ⟨max Bplus Bminus, hBplus.trans (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact (hminus x).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))
  · rw [abs_of_nonpos (lt_of_not_ge hx).le, neg_mul_neg]
    exact (hplus x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))

end ArtinPrimitiveRoots.Proofs.thsol_smooth
