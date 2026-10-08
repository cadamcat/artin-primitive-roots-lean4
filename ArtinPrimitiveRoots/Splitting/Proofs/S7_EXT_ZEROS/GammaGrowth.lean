import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaRatio

set_option autoImplicit false

open Set Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Strip digamma bounds control the reciprocal Gamma function by a quadratic exponential. -/
theorem inverse_gamma_quadratic_growth_on_strip {a b : ℝ} (ha : 0 < a)
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, a ≤ u.re → u.re ≤ b →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2) := by
  obtain ⟨C, hC, hdigamma⟩ := hdigamma
  have hcont : Continuous (fun x : ℝ => ‖(Complex.Gamma (x : ℂ))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal).norm
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image hcont.continuousOn
  refine ⟨|B| + C + 1, by positivity, ?_⟩
  intro z hza hzb
  let x : ℂ := (z.re : ℂ)
  have hanchor : ‖(Complex.Gamma x)⁻¹‖ ≤ Real.exp |B| := by
    have hbound : ‖(Complex.Gamma x)⁻¹‖ ≤ B :=
      hB (mem_image_of_mem _ ⟨hza, hzb⟩)
    exact hbound.trans (by linarith [le_abs_self B, Real.add_one_le_exp |B|])
  have hre (u : ℂ) (hu : u ∈ segment ℝ z x) : u.re = z.re := by
    rw [segment_eq_image ℝ z x] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    simp [x, Complex.real_smul]
    ring
  have him (u : ℂ) (hu : u ∈ segment ℝ z x) : |u.im| ≤ |z.im| := by
    rw [segment_eq_image ℝ z x] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    simp only [Complex.real_smul, Complex.add_im, Complex.im_ofReal_mul,
      x, Complex.ofReal_im, mul_zero, add_zero, abs_mul, abs_of_nonneg ht1]
    nlinarith [ht.1, abs_nonneg z.im]
  have hdiff (u : ℂ) (hu : u ∈ segment ℝ z x) :
      DifferentiableAt ℂ Complex.Gamma u := by
    apply Complex.differentiableAt_Gamma u
    intro n hn
    have hru : u.re = -(n : ℝ) := by simpa using congrArg Complex.re hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hre u hu]
  have hne (u : ℂ) (hu : u ∈ segment ℝ z x) : Complex.Gamma u ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [hre u hu]; linarith)
  have hlogder (u : ℂ) (hu : u ∈ segment ℝ z x) :
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|z.im| + 2) := by
    have hua : a ≤ u.re := by rw [hre u hu]; exact hza
    have hub : u.re ≤ b := by rw [hre u hu]; exact hzb
    refine (hdigamma u hua hub).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.log_le_log (by positivity)
    linarith [him u hu]
  have hdist : ‖x - z‖ = |z.im| := by
    have heq : x - z = -(z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [x]
    simp [heq]
  have hratio : ‖Complex.Gamma x / Complex.Gamma z‖ ≤
      Real.exp (C * Real.log (|z.im| + 2) * |z.im|) := by
    simpa only [hdist] using norm_ratio_le_exp_of_logDeriv_bound hdiff hne hlogder
  have hxne : Complex.Gamma x ≠ 0 := hne x (right_mem_segment ℝ z x)
  have hid : (Complex.Gamma z)⁻¹ =
      (Complex.Gamma x)⁻¹ * (Complex.Gamma x / Complex.Gamma z) := by
    simp [div_eq_mul_inv, hxne]
  have hlog0 : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlogle : Real.log (|z.im| + 2) ≤ ‖z‖ + 1 :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by
      linarith [Complex.abs_im_le_norm z])
  have hquad : |z.im| * Real.log (|z.im| + 2) ≤ (‖z‖ + 1) ^ 2 := by
    calc
      |z.im| * Real.log (|z.im| + 2) ≤ ‖z‖ * (‖z‖ + 1) :=
        mul_le_mul (Complex.abs_im_le_norm z) hlogle hlog0 (norm_nonneg z)
      _ ≤ (‖z‖ + 1) ^ 2 := by nlinarith [norm_nonneg z]
  have hsq1 : 1 ≤ (‖z‖ + 1) ^ 2 := by nlinarith [norm_nonneg z]
  calc
    ‖(Complex.Gamma z)⁻¹‖ =
        ‖(Complex.Gamma x)⁻¹‖ * ‖Complex.Gamma x / Complex.Gamma z‖ := by
      rw [hid, norm_mul]
    _ ≤ Real.exp |B| * Real.exp (C * Real.log (|z.im| + 2) * |z.im|) :=
      mul_le_mul hanchor hratio (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (|B| + C * (|z.im| * Real.log (|z.im| + 2))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((|B| + C + 1) * (‖z‖ + 1) ^ 2) := by
      apply Real.exp_le_exp.mpr
      calc
        |B| + C * (|z.im| * Real.log (|z.im| + 2)) ≤
            |B| * (‖z‖ + 1) ^ 2 + C * (‖z‖ + 1) ^ 2 :=
          add_le_add (by nlinarith [mul_le_mul_of_nonneg_left hsq1 (abs_nonneg B)])
            (mul_le_mul_of_nonneg_left hquad hC.le)
        _ ≤ (|B| + C + 1) * (‖z‖ + 1) ^ 2 := by nlinarith [sq_nonneg (‖z‖ + 1)]

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
