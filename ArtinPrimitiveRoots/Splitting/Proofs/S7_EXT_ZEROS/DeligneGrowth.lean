import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.GammaGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- The fixed shifted Deligne reciprocals have quadratic exponential growth on the Xi strip. -/
theorem shifted_deligne_inverse_quadratic_growth
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 6 →
      ‖(Complex.Gammaℝ (s + 8))⁻¹‖ ≤ Real.exp (A * (‖s‖ + 1) ^ 2) ∧
      ‖(Complex.Gammaℂ (s + 4))⁻¹‖ ≤ Real.exp (A * (‖s‖ + 1) ^ 2) := by
  obtain ⟨B, hB, hgamma⟩ :=
    inverse_gamma_quadratic_growth_on_strip (by norm_num : (0 : ℝ) < 1) hdigamma
  let L : ℝ := 10 * |Real.log Real.pi| + 10 * |Real.log (2 * Real.pi)|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨25 * B + L + 1, by positivity, ?_⟩
  have hpower {p : ℝ} (hp : 0 < p) (u : ℂ) (hu0 : 0 ≤ u.re) (hum : u.re ≤ 10) :
      ‖((p : ℂ) ^ (-u))⁻¹‖ ≤ Real.exp (10 * |Real.log p|) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hp,
      Real.rpow_def_of_pos hp, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    simp only [Complex.neg_re]
    calc
      -(Real.log p * -u.re) = u.re * Real.log p := by ring
      _ ≤ u.re * |Real.log p| := mul_le_mul_of_nonneg_left (le_abs_self _) hu0
      _ ≤ 10 * |Real.log p| := mul_le_mul_of_nonneg_right hum (abs_nonneg _)
  intro s hsa hsb
  have hargR : 1 ≤ ((s + 8) / 2).re ∧ ((s + 8) / 2).re ≤ 10 := by
    norm_num [Complex.div_ofNat_re, Complex.add_re]
    constructor <;> linarith
  have hargC : 1 ≤ (s + 4).re ∧ (s + 4).re ≤ 10 := by
    norm_num [Complex.add_re]
    constructor <;> linarith
  have hnormR : ‖(s + 8) / 2‖ + 1 ≤ 5 * (‖s‖ + 1) := by
    have hadd : ‖s + 8‖ ≤ ‖s‖ + 8 := by simpa using norm_add_le s (8 : ℂ)
    have hdiv : ‖(s + 8) / 2‖ = ‖s + 8‖ / 2 := by simp
    rw [hdiv]
    linarith [norm_nonneg s]
  have hnormC : ‖s + 4‖ + 1 ≤ 5 * (‖s‖ + 1) := by
    have hadd : ‖s + 4‖ ≤ ‖s‖ + 4 := by simpa using norm_add_le s (4 : ℂ)
    linarith [norm_nonneg s]
  have hquad (u : ℂ) (hu : ‖u‖ + 1 ≤ 5 * (‖s‖ + 1)) :
      (‖u‖ + 1) ^ 2 ≤ 25 * (‖s‖ + 1) ^ 2 := by
    calc
      (‖u‖ + 1) ^ 2 ≤ (5 * (‖s‖ + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hu 2
      _ = 25 * (‖s‖ + 1) ^ 2 := by ring
  have hGammaR : ‖(Complex.Gamma ((s + 8) / 2))⁻¹‖ ≤
      Real.exp ((25 * B) * (‖s‖ + 1) ^ 2) := by
    refine (hgamma _ hargR.1 hargR.2).trans (Real.exp_le_exp.mpr ?_)
    calc
      B * (‖(s + 8) / 2‖ + 1) ^ 2 ≤ B * (25 * (‖s‖ + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad _ hnormR) hB.le
      _ = (25 * B) * (‖s‖ + 1) ^ 2 := by ring
  have hGammaC : ‖(Complex.Gamma (s + 4))⁻¹‖ ≤
      Real.exp ((25 * B) * (‖s‖ + 1) ^ 2) := by
    refine (hgamma _ hargC.1 hargC.2).trans (Real.exp_le_exp.mpr ?_)
    calc
      B * (‖s + 4‖ + 1) ^ 2 ≤ B * (25 * (‖s‖ + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (hquad _ hnormC) hB.le
      _ = (25 * B) * (‖s‖ + 1) ^ 2 := by ring
  have hpiR : ‖((Real.pi : ℂ) ^ (-(s + 8) / 2))⁻¹‖ ≤ Real.exp L := by
    have hh := hpower Real.pi_pos ((s + 8) / 2) (by linarith [hargR.1]) hargR.2
    rw [← neg_div] at hh
    refine hh.trans (Real.exp_le_exp.mpr ?_)
    dsimp [L]
    linarith [abs_nonneg (Real.log (2 * Real.pi))]
  have hpiC : ‖(2 * (2 * (Real.pi : ℂ)) ^ (-(s + 4)))⁻¹‖ ≤ Real.exp L := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have hh := hpower hp (s + 4) (by linarith [hargC.1]) hargC.2
    have htwo : ‖(2 : ℂ)⁻¹‖ ≤ (1 : ℝ) := by norm_num
    rw [mul_inv, norm_mul]
    have hcp : ‖((2 * (Real.pi : ℂ)) ^ (-(s + 4)))⁻¹‖ ≤
        Real.exp (10 * |Real.log (2 * Real.pi)|) := by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hh
    refine (mul_le_mul htwo hcp (norm_nonneg _) (by norm_num)).trans ?_
    simp only [one_mul]
    apply Real.exp_le_exp.mpr
    dsimp [L]
    linarith [abs_nonneg (Real.log Real.pi)]
  have hfinal : Real.exp L * Real.exp ((25 * B) * (‖s‖ + 1) ^ 2) ≤
      Real.exp ((25 * B + L + 1) * (‖s‖ + 1) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq1 : 1 ≤ (‖s‖ + 1) ^ 2 := by nlinarith [norm_nonneg s]
    have hterm := mul_le_mul_of_nonneg_left hsq1 hL
    nlinarith [sq_nonneg (‖s‖ + 1)]
  constructor
  · rw [Complex.Gammaℝ_def, mul_inv, norm_mul]
    exact (mul_le_mul hpiR hGammaR (norm_nonneg _) (Real.exp_pos _).le).trans hfinal
  · rw [Complex.Gammaℂ_def, mul_inv, norm_mul]
    exact (mul_le_mul hpiC hGammaC (norm_nonneg _) (Real.exp_pos _).le).trans hfinal

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
