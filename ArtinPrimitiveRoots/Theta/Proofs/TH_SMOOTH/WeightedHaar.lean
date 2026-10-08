import ArtinPrimitiveRoots.Theta.Proofs.TH_SMOOTH.LocalMellin
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
noncomputable section

open MeasureTheory
open ArtinPrimitiveRoots.A1

namespace ArtinPrimitiveRoots.Proofs.thsol_smooth

private theorem radial_withDensity (f : ℝ → ℂ) :
    (Integrable (fun z : ℂ => (Complex.normSq z : ℂ) * f (Complex.normSq z))
      (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹))) ↔
        IntegrableOn f (Set.Ioi 0)) ∧
    (∫ z : ℂ, (Complex.normSq z : ℂ) * f (Complex.normSq z)
      ∂(volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹)))) =
        (Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), f t := by
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹)) := by
    fun_prop
  have hfinite : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal ((Complex.normSq z)⁻¹) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by simp [ae_iff]
  have heq : (fun z : ℂ => (ENNReal.ofReal ((Complex.normSq z)⁻¹)).toReal •
      ((Complex.normSq z : ℂ) * f (Complex.normSq z))) =ᵐ[volume]
        (fun z : ℂ => f (‖z‖ ^ 2)) := by
    filter_upwards [hne] with z hz
    have hn : Complex.normSq z ≠ 0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hnonneg : 0 ≤ (Complex.normSq z)⁻¹ := by
      apply inv_nonneg.mpr
      rw [Complex.normSq_eq_norm_sq]
      exact sq_nonneg _
    rw [ENNReal.toReal_ofReal hnonneg, Complex.real_smul, Complex.ofReal_inv,
      inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hn), Complex.normSq_eq_norm_sq]
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hd hfinite]
    exact (integrable_congr heq).trans (OAI.CubicEisenstein.integrable_radial_sq_iff f)
  · rw [integral_withDensity_eq_integral_toReal_smul hd hfinite]
    exact (integral_congr_ae heq).trans (OAI.CubicEisenstein.integral_radial_sq f)

/-- A Mellin-weighted complex Bessel factor is integrable for multiplicative Haar measure,
and its integral is pi times the radial Mellin factor. -/
theorem bessel_complex_mellin (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun z : ℂ => (Complex.normSq z : ℂ) ^ s * (Complex.normSq z : ℂ) *
      (besselK (1 / 3) (c * ‖z‖) : ℂ))
      (volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹))) ∧
    (∫ z : ℂ, (Complex.normSq z : ℂ) ^ s * (Complex.normSq z : ℂ) *
      (besselK (1 / 3) (c * ‖z‖) : ℂ)
      ∂(volume.withDensity (fun z : ℂ => ENNReal.ofReal ((Complex.normSq z)⁻¹)))) =
        (Real.pi : ℂ) * ((2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
          Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ s * (besselK (1 / 3) (c * Real.sqrt t) : ℂ)
  have hpow (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ s := by
    calc
      (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = (t : ℂ) ^ s := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))]
        congr 1
        ring
  have heq : ∀ t ∈ Set.Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * ((t : ℂ) * (besselK (1 / 3) (c * Real.sqrt t) : ℂ)) = f t := by
    intro t ht
    rw [← mul_assoc, hpow t ht]
  obtain ⟨hi, hvalue⟩ := bessel_radial_hasMellin c hc s hs
  have hfi : IntegrableOn f (Set.Ioi 0) := hi.congr_fun heq measurableSet_Ioi
  have hval : (∫ t in Set.Ioi (0 : ℝ), f t) =
      (2 : ℂ) ^ (2 * s + 1) * (c : ℂ) ^ (-2 * s - 2) *
        Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) :=
    (setIntegral_congr_fun measurableSet_Ioi heq).symm.trans hvalue
  have hfun : (fun z : ℂ => (Complex.normSq z : ℂ) * f (Complex.normSq z)) =
      (fun z : ℂ => (Complex.normSq z : ℂ) ^ s * (Complex.normSq z : ℂ) *
        (besselK (1 / 3) (c * ‖z‖) : ℂ)) := by
    funext z
    dsimp only [f]
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
    ring
  obtain ⟨hiff, hint⟩ := radial_withDensity f
  constructor
  · rw [← hfun]
    exact hiff.mpr hfi
  · rw [← hfun, hint, hval]

end ArtinPrimitiveRoots.Proofs.thsol_smooth
