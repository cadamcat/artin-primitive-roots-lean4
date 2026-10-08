import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.Moments
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

/-- The integrand for the logarithmic inverse Mellin transform and its derivatives. -/
def smoothingIntegrand (C A : ℝ) (r j : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  s ^ j * smoothingQuotient C A r s * Complex.exp (s * (x : ℂ))

private theorem vertical_integral_shift (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (hgi : Integrable g)
    (hgt : Tendsto g atTop (𝓝 0)) (hgb : Tendsto g atBot (𝓝 0))
    (hbound : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ g s.im) :
    (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I) := by
  have hline (c : ℝ) (hca : a ≤ c) (hcb : c ≤ b) :
      Integrable (fun t : ℝ => f ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hc : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    apply hgi.mono' (hf.continuous.comp hc).aestronglyMeasurable
    filter_upwards [] with t
    simpa using hbound ((c : ℂ) + (t : ℂ) * Complex.I) (by simpa using hca)
      (by simpa using hcb)
  let H (t : ℝ) : ℂ := ∫ u : ℝ in a..b, f ((u : ℂ) + (t : ℂ) * Complex.I)
  have hH (t : ℝ) : ‖H t‖ ≤ g t * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    simpa using hbound ((u : ℂ) + (t : ℂ) * Complex.I) (by simpa using hu.1.le)
      (by simpa using hu.2)
  have hHt : Tendsto H atTop (𝓝 0) :=
    squeeze_zero_norm hH (by simpa using hgt.mul_const |b - a|)
  have hHb : Tendsto (fun T : ℝ => H (-T)) atTop (𝓝 0) :=
    (squeeze_zero_norm hH (by simpa using hgb.mul_const |b - a|)).comp
      tendsto_neg_atTop_atBot
  have hta := intervalIntegral_tendsto_integral (hline a le_rfl hab)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have htb := intervalIntegral_tendsto_integral (hline b hab le_rfl)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hrect (T : ℝ) : H (-T) - H T +
      Complex.I * (∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
    have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
      hf.differentiableOn
    simpa [H, smul_eq_mul] using hh
  have hlim := ((hHb.sub hHt).add (htb.const_mul Complex.I)).sub (hta.const_mul Complex.I)
  have hlim₀ : Tendsto (fun T : ℝ => H (-T) - H T +
      Complex.I * (∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun T => (hrect T).symm)
  have hh : Complex.I * (∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
    simpa using tendsto_nhds_unique hlim hlim₀
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp hh)).symm

/-- The inverse transform and all of its formal log derivatives are absolutely
integrable and independent of the chosen vertical line. -/
theorem smoothing_quotient_contour (C A : ℝ) (hC : 0 < C) (hA : 0 < A) (r j : ℕ)
    (x : ℝ) :
    (∀ σ : ℝ, Integrable (fun t : ℝ =>
      smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
      (∀ σ τ : ℝ,
        (∫ t : ℝ, smoothingIntegrand C A r j x ((σ : ℂ) + (t : ℂ) * Complex.I)) =
          ∫ t : ℝ, smoothingIntegrand C A r j x ((τ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hf : Differentiable ℂ (smoothingIntegrand C A r j x) := by
    exact ((differentiable_id.pow j).mul
      (smoothing_quotient_control C A hC hA r).1).mul
        (differentiable_id.mul_const (x : ℂ)).cexp
  have henv (a b : ℝ) : ∃ k : ℝ → ℝ, Integrable k ∧
      Tendsto k atTop (𝓝 0) ∧ Tendsto k atBot (𝓝 0) ∧
      (∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖smoothingIntegrand C A r j x s‖ ≤ k s.im) := by
    obtain ⟨g, hg, hgi, hgt, hgb, hbound, _⟩ :=
      smoothing_quotient_moments C A hC hA r a b j
    let R : ℝ := |a| + |b|
    let D : ℝ := Real.exp (R * |x|)
    refine ⟨fun t => D * g t, hgi.const_mul D, ?_, ?_, ?_⟩
    · simpa only [mul_zero] using hgt.const_mul D
    · simpa only [mul_zero] using hgb.const_mul D
    · intro s hsa hsb
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
      have hexp : Real.exp (s.re * x) ≤ D := by
        apply Real.exp_le_exp.mpr
        calc
          s.re * x ≤ |s.re * x| := le_abs_self _
          _ = |s.re| * |x| := abs_mul _ _
          _ ≤ R * |x| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
      calc
        ‖smoothingIntegrand C A r j x s‖ =
            ‖s ^ j * smoothingQuotient C A r s‖ * Real.exp (s.re * x) := by
          simp only [smoothingIntegrand, norm_mul, Complex.norm_exp,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        _ ≤ g s.im * D :=
          mul_le_mul (hbound s hsa hsb) hexp (Real.exp_nonneg _) (hg _)
        _ = D * g s.im := mul_comm _ _
  constructor
  · intro σ
    obtain ⟨k, hki, _, _, hbound⟩ := henv σ σ
    have hc : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    apply hki.mono' (hf.continuous.comp hc).aestronglyMeasurable
    filter_upwards [] with t
    simpa using hbound ((σ : ℂ) + (t : ℂ) * Complex.I) (by simp) (by simp)
  · intro σ τ
    rcases le_total σ τ with hστ | hτσ
    · obtain ⟨k, hki, hkt, hkb, hbound⟩ := henv σ τ
      exact vertical_integral_shift (smoothingIntegrand C A r j x) hf σ τ hστ
        k hki hkt hkb hbound
    · obtain ⟨k, hki, hkt, hkb, hbound⟩ := henv τ σ
      exact (vertical_integral_shift (smoothingIntegrand C A r j x) hf τ σ hτσ
        k hki hkt hkb hbound).symm

end ArtinPrimitiveRoots.Proofs.thsol_smooth
