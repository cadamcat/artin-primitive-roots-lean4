import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Quotient
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem gaussian_moment (j : ℕ) :
    Integrable (fun t : ℝ => |t| ^ j * Real.exp (-(t ^ 2) / 2)) ∧
      Tendsto (fun t : ℝ => |t| ^ j * Real.exp (-(t ^ 2) / 2)) atTop (𝓝 0) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num) (s := (j : ℝ))
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg j))
  have he : Tendsto (fun t : ℝ => Real.exp (-(1 / 2) * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)).mpr tendsto_id)
  have ht := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
    (b := (1 / 2 : ℝ)) (by norm_num) (j : ℝ)).trans_tendsto he
  constructor
  · convert hi.norm using 1
    ext t
    rw [Real.norm_eq_abs, abs_mul, Real.rpow_natCast, abs_pow,
      abs_of_pos (Real.exp_pos _)]
    rw [show -(t ^ 2) / 2 = -(1 / 2 : ℝ) * t ^ 2 by ring]
  · convert ht.norm using 1
    · ext t
      rw [Real.norm_eq_abs, abs_mul, Real.rpow_natCast, abs_pow,
        abs_of_pos (Real.exp_pos _)]
      rw [show -(t ^ 2) / 2 = -(1 / 2 : ℝ) * t ^ 2 by ring]
    · simp

/-- Polynomial-weighted vertical quotients have an integrable strip-uniform envelope
that vanishes at both ends of the imaginary axis. -/
theorem smoothing_quotient_moments (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r : ℕ)
    (a b : ℝ) (j : ℕ) :
    ∃ g : ℝ → ℝ, (∀ t, 0 ≤ g t) ∧ Integrable g ∧
      Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) ∧
      (∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖s ^ j * smoothingQuotient C A r s‖ ≤ g s.im) ∧
      (∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable (fun t : ℝ =>
        ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j *
          smoothingQuotient C A r ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  obtain ⟨hqdiff, _, hstrip⟩ := smoothing_quotient_control C A hC hA r
  obtain ⟨B, hB, hbound⟩ := hstrip a b
  let R : ℝ := |a| + |b|
  let g (t : ℝ) : ℝ := (B * 2 ^ (j - 1)) *
    (R ^ j * Real.exp (-(t ^ 2) / 2) + |t| ^ j * Real.exp (-(t ^ 2) / 2))
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨hi₀, ht₀⟩ := gaussian_moment 0
  simp only [pow_zero, one_mul] at hi₀ ht₀
  obtain ⟨hiⱼ, htⱼ⟩ := gaussian_moment j
  have hgi : Integrable g :=
    ((hi₀.const_mul (R ^ j)).add hiⱼ).const_mul (B * 2 ^ (j - 1))
  have hgtop : Tendsto g atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      ((ht₀.const_mul (R ^ j)).add htⱼ).const_mul (B * 2 ^ (j - 1))
  have hgbot : Tendsto g atBot (𝓝 0) := by
    simpa only [Function.comp_def, g, abs_neg, neg_sq] using
      hgtop.comp tendsto_neg_atBot_atTop
  have hg (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
      ‖s ^ j * smoothingQuotient C A r s‖ ≤ g s.im := by
    have hre : |s.re| ≤ R := by
      apply abs_le.mpr
      constructor
      · have ha := neg_abs_le a
        have hb := abs_nonneg b
        dsimp only [R]
        linarith
      · have ha := abs_nonneg a
        have hb := le_abs_self b
        dsimp only [R]
        linarith
    have hnorm : ‖s‖ ≤ R + |s.im| :=
      (Complex.norm_le_abs_re_add_abs_im s).trans (add_le_add hre le_rfl)
    have hpow : ‖s‖ ^ j ≤ 2 ^ (j - 1) * (R ^ j + |s.im| ^ j) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm j).trans
        (add_pow_le hR (abs_nonneg _) j)
    calc
      ‖s ^ j * smoothingQuotient C A r s‖ =
          ‖s‖ ^ j * ‖smoothingQuotient C A r s‖ := by rw [norm_mul, norm_pow]
      _ ≤ (2 ^ (j - 1) * (R ^ j + |s.im| ^ j)) *
          (B * Real.exp (-(s.im ^ 2) / 2)) :=
        mul_le_mul hpow (hbound s hsa hsb) (norm_nonneg _) (by positivity)
      _ = g s.im := by dsimp only [g]; ring
  refine ⟨g, (fun t => by dsimp only [g]; positivity), hgi, hgtop, hgbot, hg, ?_⟩
  intro σ hσa hσb
  have hz : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  apply hgi.mono' ((hz.pow j).mul (hqdiff.continuous.comp hz)).aestronglyMeasurable
  filter_upwards [] with t
  simpa using hg ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσa)
    (by simpa using hσb)

end ArtinPrimitiveRoots.Proofs.thsol_smooth
