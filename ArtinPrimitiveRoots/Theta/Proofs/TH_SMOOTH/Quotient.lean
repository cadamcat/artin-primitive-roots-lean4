import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.ReciprocalGamma

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The entire quotient used to invert the theta Mellin transform. -/
def smoothingQuotient (C A : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (C : ℂ)⁻¹ * Complex.exp (s ^ 2 - s * (Real.log A : ℂ)) *
    ((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ r

private theorem quotient_entire (C A : ℝ) (r : ℕ) :
    Differentiable ℂ (smoothingQuotient C A r) := by
  have h₁ := Complex.differentiable_one_div_Gamma.comp
    (differentiable_id.add_const (5 / 6 : ℂ))
  have h₂ := Complex.differentiable_one_div_Gamma.comp
    (differentiable_id.add_const (7 / 6 : ℂ))
  exact ((differentiable_const _).mul
    (((differentiable_id.pow 2).sub (differentiable_id.mul_const _)).cexp)).mul
      ((h₁.mul h₂).pow r)

private theorem quotient_formula (C A : ℝ) (hA : 0 < A) (r : ℕ) (s : ℂ) :
    smoothingQuotient C A r s =
      Complex.exp (s ^ 2) / ((C : ℂ) * (A : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r) := by
  dsimp only [smoothingQuotient]
  rw [Complex.exp_sub, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne'),
    ← Complex.ofReal_log hA.le, mul_comm (Real.log A : ℂ) s]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_pow]
  ring

private theorem quotient_strip_bound (C A : ℝ) (hC : 0 < C) (r : ℕ) (a b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖smoothingQuotient C A r s‖ ≤ B * Real.exp (-(s.im ^ 2) / 2) := by
  obtain ⟨G₁, hG₁, hg₁⟩ := th_smooth_part2 (a + 5 / 6) (b + 5 / 6)
  obtain ⟨G₂, hG₂, hg₂⟩ := th_smooth_part2 (a + 7 / 6) (b + 7 / 6)
  let R : ℝ := |a| + |b|
  let D : ℝ := R ^ 2 + R * |Real.log A|
  let p : ℝ := Real.pi * r
  let B : ℝ := C⁻¹ * (G₁ * G₂) ^ r * Real.exp (D + 2 * p ^ 2)
  refine ⟨B, by dsimp only [B]; positivity, ?_⟩
  intro s hsa hsb
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hre : |s.re| ≤ R := by
    apply abs_le.mpr
    constructor
    · have ha := neg_abs_le a
      have hb := abs_nonneg b
      dsimp [R]
      linarith
    · have ha := abs_nonneg a
      have hb := le_abs_self b
      dsimp [R]
      linarith
  have hsquare : s.re ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s.re) hR).mpr hre
  have hlog : -(s.re * Real.log A) ≤ R * |Real.log A| := by
    calc
      -(s.re * Real.log A) ≤ |s.re * Real.log A| := neg_le_abs _
      _ = |s.re| * |Real.log A| := abs_mul _ _
      _ ≤ R * |Real.log A| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have he : (s ^ 2 - s * (Real.log A : ℂ)).re ≤ D - s.im ^ 2 := by
    simp only [pow_two, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp only [D]
    nlinarith
  have h₁ : ‖(Complex.Gamma (s + 5 / 6))⁻¹‖ ≤
      G₁ * Real.exp (Real.pi * |s.im|) := by
    have hh := hg₁ (s + 5 / 6)
      (by norm_num [Complex.add_re]; linarith)
      (by norm_num [Complex.add_re]; linarith)
    simpa using hh
  have h₂ : ‖(Complex.Gamma (s + 7 / 6))⁻¹‖ ≤
      G₂ * Real.exp (Real.pi * |s.im|) := by
    have hh := hg₂ (s + 7 / 6)
      (by norm_num [Complex.add_re]; linarith)
      (by norm_num [Complex.add_re]; linarith)
    simpa using hh
  have hg : ‖(Complex.Gamma (s + 5 / 6))⁻¹ *
      (Complex.Gamma (s + 7 / 6))⁻¹‖ ≤
        G₁ * G₂ * Real.exp (2 * Real.pi * |s.im|) := by
    rw [norm_mul]
    calc
      _ ≤ (G₁ * Real.exp (Real.pi * |s.im|)) *
          (G₂ * Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show 2 * Real.pi * |s.im| =
          Real.pi * |s.im| + Real.pi * |s.im| by ring, Real.exp_add]
        ring
  have hcomplete : D - s.im ^ 2 + (r : ℝ) * (2 * Real.pi * |s.im|) ≤
      D + 2 * p ^ 2 - s.im ^ 2 / 2 := by
    have hsq := sq_nonneg (|s.im| - 2 * p)
    dsimp only [p] at *
    nlinarith [sq_abs s.im]
  calc
    ‖smoothingQuotient C A r s‖ = C⁻¹ *
        Real.exp ((s ^ 2 - s * (Real.log A : ℂ)).re) *
          ‖(Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹‖ ^ r := by
      simp only [smoothingQuotient, norm_mul, norm_inv,
        Complex.norm_of_nonneg hC.le, Complex.norm_exp, norm_pow]
    _ ≤ C⁻¹ * Real.exp (D - s.im ^ 2) *
        (G₁ * G₂ * Real.exp (2 * Real.pi * |s.im|)) ^ r := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))
        (pow_le_pow_left₀ (norm_nonneg _) hg r) (by positivity) (by positivity)
    _ = C⁻¹ * (G₁ * G₂) ^ r *
        Real.exp (D - s.im ^ 2 + (r : ℝ) * (2 * Real.pi * |s.im|)) := by
      rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]
      ring
    _ ≤ C⁻¹ * (G₁ * G₂) ^ r *
        Real.exp (D + 2 * p ^ 2 - s.im ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomplete) (by positivity)
    _ = B * Real.exp (-(s.im ^ 2) / 2) := by
      dsimp only [B]
      rw [sub_eq_add_neg, Real.exp_add, neg_div]
      ring

/-- The quotient is entire, equals the prescribed reciprocal Mellin expression,
and is uniformly dominated by a Gaussian on every closed vertical strip. -/
theorem smoothing_quotient_control (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r : ℕ) :
    Differentiable ℂ (smoothingQuotient C A r) ∧
      (∀ s : ℂ, smoothingQuotient C A r s =
        Complex.exp (s ^ 2) / ((C : ℂ) * (A : ℂ) ^ s *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r)) ∧
      (∀ a b : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖smoothingQuotient C A r s‖ ≤ B * Real.exp (-(s.im ^ 2) / 2)) := by
  exact ⟨quotient_entire C A r, quotient_formula C A hA r,
    quotient_strip_bound C A hC r⟩

end ArtinPrimitiveRoots.Proofs.thsol_smooth
