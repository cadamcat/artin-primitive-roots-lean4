import ArtinPrimitiveRoots.TypeII.PD.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical MeasureTheory FourierTransform
open ArtinPrimitiveRoots.TypeII

/-- The ordinary Fourier transform of the smooth determinant cutoff. -/
def pd4c_psiHat (ψ : ℝ → ℝ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, (ψ t : ℂ) * additiveCharacter (-u * t)

private def pd4c_psiSchwartz (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ) :
    SchwartzMap ℝ ℂ := by
  have hsupport : Function.support (fun t => (ψ t : ℂ)) = Function.support ψ := by
    ext t
    simp
  have hcompactC : HasCompactSupport (fun t => (ψ t : ℂ)) := by
    change IsCompact (closure (Function.support (fun t => (ψ t : ℂ))))
    rw [hsupport]
    exact hcompact
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => (ψ t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  exact hcompactC.toSchwartzMap hsmooth

private theorem pd4c_psiHat_fourier (ψ : ℝ → ℝ) (u : ℝ) :
    pd4c_psiHat ψ u = 𝓕 (fun t : ℝ => (ψ t : ℂ)) u := by
  unfold pd4c_psiHat
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Real.inner_apply]
  simp only [smul_eq_mul]
  unfold additiveCharacter
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- A compact smooth cutoff has a Schwartz Fourier density. -/
theorem pd4c_psiHat_isSchwartz (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ) :
    ∃ H : SchwartzMap ℝ ℂ, (H : ℝ → ℂ) = pd4c_psiHat ψ := by
  let S := pd4c_psiSchwartz ψ hψ hcompact
  refine ⟨𝓕 S, ?_⟩
  funext u
  exact (pd4c_psiHat_fourier ψ u).symm

/-- Every polynomially weighted norm of the Fourier density is integrable. -/
theorem pd4c_psiHat_integrable_pow (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ) (N : ℕ) :
    Integrable (fun u : ℝ => |u| ^ N * ‖pd4c_psiHat ψ u‖) := by
  obtain ⟨H, hH⟩ := pd4c_psiHat_isSchwartz ψ hψ hcompact
  simpa only [Real.norm_eq_abs, hH] using H.integrable_pow_mul volume N

/-- Ordinary Fourier inversion supplies the determinant cutoff identity. -/
theorem pd4c_psiHat_inversion (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ) (x : ℝ) :
    (ψ x : ℂ) = ∫ u : ℝ, pd4c_psiHat ψ u * additiveCharacter (u * x) := by
  let S := pd4c_psiSchwartz ψ hψ hcompact
  have hS : (S : ℝ → ℂ) = fun t => (ψ t : ℂ) := rfl
  have hinv := S.continuous.fourierInv_fourier_eq S.integrable (𝓕 S).integrable
  have hpoint := congrFun hinv x
  calc
    _ = (𝓕⁻ (𝓕 (fun t : ℝ => (ψ t : ℂ)))) x := by simpa only [hS] using hpoint.symm
    _ = _ := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Real.inner_apply, ← pd4c_psiHat_fourier]
      simp only [smul_eq_mul]
      unfold additiveCharacter
      rw [mul_comm]
      congr 1
      congr 1
      push_cast
      ring

/-- Weighted integrability gives any inverse-power bound for the Fourier tail. -/
theorem pd4c_psiHat_tail (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (N : ℕ) (R : ℝ) (hR : 0 < R) :
    (∫ u : ℝ in {u | R < |u|}, ‖pd4c_psiHat ψ u‖) ≤
      (∫ u : ℝ, |u| ^ N * ‖pd4c_psiHat ψ u‖) / R ^ N := by
  have hi := pd4c_psiHat_integrable_pow ψ hψ hcompact N
  have hinorm : Integrable (fun u : ℝ => ‖pd4c_psiHat ψ u‖) := by
    simpa using pd4c_psiHat_integrable_pow ψ hψ hcompact 0
  have hmeas : MeasurableSet {u : ℝ | R < |u|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hpow : 0 < R ^ N := pow_pos hR N
  have hpoint (u : ℝ) (hu : R < |u|) :
      ‖pd4c_psiHat ψ u‖ ≤ (|u| ^ N * ‖pd4c_psiHat ψ u‖) / R ^ N := by
    apply (le_div_iff₀ hpow).2
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hu.le N) (norm_nonneg (pd4c_psiHat ψ u))
    simpa only [mul_comm] using h
  calc
    _ ≤ ∫ u : ℝ in {u | R < |u|}, (|u| ^ N * ‖pd4c_psiHat ψ u‖) / R ^ N := by
      apply integral_mono_ae hinorm.integrableOn (hi.div_const _).integrableOn
      filter_upwards [ae_restrict_mem hmeas] with u hu
      exact hpoint u hu
    _ = (∫ u : ℝ in {u | R < |u|}, |u| ^ N * ‖pd4c_psiHat ψ u‖) / R ^ N := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right
      (setIntegral_le_integral hi (Filter.Eventually.of_forall fun u =>
        mul_nonneg (pow_nonneg (abs_nonneg u) N) (norm_nonneg _))) hpow.le

private theorem pd4c_additiveCharacter_add (a b : ℝ) :
    additiveCharacter a * additiveCharacter b = additiveCharacter (a + b) := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The smoothed determinant character is the integral of shifted determinant characters. -/
theorem pd4c_determinant_cutoff_fourier (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (Y θ t : ℝ) :
    (ψ (t / Y) : ℂ) * additiveCharacter (θ * t) =
      ∫ u : ℝ, pd4c_psiHat ψ u * additiveCharacter ((θ + u / Y) * t) := by
  rw [pd4c_psiHat_inversion ψ hψ hcompact (t / Y), ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [mul_assoc, pd4c_additiveCharacter_add]
  congr 2
  ring

end

end ArtinPrimitiveRoots.TypeII.PD
