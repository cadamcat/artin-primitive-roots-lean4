import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem gamma_norm_le_real {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), ‖(Real.exp (-t) : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp

private theorem sin_norm_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num only [Complex.norm_ofNat]
  have h₁ : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using le_abs_self z.im
  have h₂ : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_abs z.im
  have hh := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  linarith

private theorem inv_gamma_reflection {z : ℂ} (hz : z.re < 1) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have hpos : 0 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hg₁ := Complex.Gamma_ne_zero_of_re_pos hpos
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr := Complex.Gamma_mul_Gamma_one_sub z
  by_cases hs : Complex.sin (Real.pi * z) = 0
  · rw [hs, div_zero] at hr
    have hg : Complex.Gamma z = 0 := (mul_eq_zero.mp hr).resolve_right hg₁
    simp [hg, hs]
  · have hcross := (eq_div_iff hs).mp hr
    have hg : Complex.Gamma z ≠ 0 := by
      intro h
      simp [h] at hcross
      exact hp hcross.symm
    apply (eq_div_iff hp).mpr
    calc
      (Complex.Gamma z)⁻¹ * (Real.pi : ℂ) =
          (Complex.Gamma z)⁻¹ *
            (Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (Real.pi * z)) :=
        congrArg ((Complex.Gamma z)⁻¹ * ·) hcross.symm
      _ = Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]

private theorem inv_gamma_norm_add_nat_le (z : ℂ) (hz : 1 ≤ |z.im|) (n : ℕ) :
    ‖(Complex.Gamma (z + n))⁻¹‖ ≤ ‖(Complex.Gamma z)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 1 ≤ ‖z + (n : ℂ)‖ := by
      have hh := Complex.abs_im_le_norm (z + (n : ℂ))
      simp only [Complex.add_im, Complex.natCast_im, add_zero] at hh
      exact hz.trans hh
    have hh : ‖(Complex.Gamma ((z + n) + 1))⁻¹‖ ≤ ‖(Complex.Gamma (z + n))⁻¹‖ := by
      calc
        ‖(Complex.Gamma ((z + n) + 1))⁻¹‖ ≤
            ‖z + (n : ℂ)‖ * ‖(Complex.Gamma ((z + n) + 1))⁻¹‖ :=
          le_mul_of_one_le_left (norm_nonneg _) hn
        _ = ‖(Complex.Gamma (z + n))⁻¹‖ := by
          rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n), norm_mul]
    simpa only [Nat.cast_succ, add_assoc] using hh.trans ih

/-- Reciprocal Gamma grows at most exponentially in the imaginary coordinate on every
closed real strip, including Mathlib's totalized values at the Gamma poles. -/
theorem th_smooth_part2 (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hlow : 0 < 1 - b + (n : ℝ) := by linarith
  have hGcont : ContinuousOn Real.Gamma (Set.Icc (1 - b + (n : ℝ)) (1 - a + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx
      exact hlow.trans_le hx.1)
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image hGcont
  have hGbound : ∀ x ∈ Set.Icc (1 - b + (n : ℝ)) (1 - a + n), Real.Gamma x ≤ max G 0 := by
    intro x hx
    exact (hG (Set.mem_image_of_mem Real.Gamma hx)).trans (le_max_left _ _)
  let R : ℝ := |a| + |b| + 1
  have hcont : Continuous (fun z : ℂ => ‖(Complex.Gamma z)⁻¹‖) :=
    Complex.differentiable_one_div_Gamma.continuous.norm
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hcont.continuousOn
  let C : ℝ := max (max B 0) (max G 0 / Real.pi)
  refine ⟨C, (le_max_right B 0).trans (le_max_left _ _), ?_⟩
  intro z hza hzb
  have hexp : 1 ≤ Real.exp (Real.pi * |z.im|) :=
    Real.one_le_exp_iff.mpr (mul_nonneg Real.pi_pos.le (abs_nonneg _))
  by_cases him : |z.im| ≤ 1
  · have hre : |z.re| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · have ha := neg_abs_le a
        have hb := abs_nonneg b
        linarith
      · have ha := abs_nonneg a
        have hb := le_abs_self b
        linarith
    have hzR : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by dsimp [R]; linarith)
    have hsmall : ‖(Complex.Gamma z)⁻¹‖ ≤ C :=
      (hB (Set.mem_image_of_mem _ hzR)).trans ((le_max_left B 0).trans (le_max_left _ _))
    exact hsmall.trans (le_mul_of_one_le_right (by dsimp [C]; positivity) hexp)
  · let w : ℂ := z - n
    have hwre : w.re < 1 := by
      change z.re - (n : ℝ) < 1
      linarith
    have hwim : w.im = z.im := by simp [w]
    have hwrange : (1 - w).re ∈ Set.Icc (1 - b + (n : ℝ)) (1 - a + n) := by
      change 1 - (z.re - (n : ℝ)) ∈ Set.Icc (1 - b + (n : ℝ)) (1 - a + n)
      constructor <;> linarith
    have hGamma : ‖Complex.Gamma (1 - w)‖ ≤ max G 0 :=
      (gamma_norm_le_real (hlow.trans_le hwrange.1)).trans (hGbound _ hwrange)
    have hsin : ‖Complex.sin (Real.pi * w)‖ ≤ Real.exp (Real.pi * |z.im|) := by
      have hh := sin_norm_le_exp (Real.pi * w)
      simpa [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos, hwim] using hh
    have hleft : ‖(Complex.Gamma w)⁻¹‖ ≤ (max G 0 / Real.pi) * Real.exp (Real.pi * |z.im|) := by
      rw [inv_gamma_reflection hwre, norm_div, norm_mul,
        Complex.norm_of_nonneg Real.pi_pos.le]
      calc
        ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin (Real.pi * w)‖ / Real.pi ≤
            (max G 0 * Real.exp (Real.pi * |z.im|)) / Real.pi := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul hGamma hsin (norm_nonneg _) (le_max_right _ _)) Real.pi_pos.le
        _ = (max G 0 / Real.pi) * Real.exp (Real.pi * |z.im|) := by ring
    have hshift : ‖(Complex.Gamma z)⁻¹‖ ≤ ‖(Complex.Gamma w)⁻¹‖ := by
      have hh := inv_gamma_norm_add_nat_le w (by rw [hwim]; exact (lt_of_not_ge him).le) n
      simpa [w] using hh
    exact (hshift.trans hleft).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))

end ArtinPrimitiveRoots.Proofs.thsol_smooth
