import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_unit_box_inversion
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_dual_ideal_norm


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Normalize the weighted unit-box Poisson equation by the ideal norm and discriminant.
Guide: sol-thin-hk2/PROOFS.md:1426–1445. Uses hk_weighted_unit_box_inversion,
hk_dual_ideal_norm and heckeBeta; conductor exponent is one half. LEAD. -/
theorem hk_weighted_normalized_inversion [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (I : NumberFieldFractionalIdealGroup K) {t : ℝ} (ht : 0 < t) :
    hkNormalizedG ψ I (1 / t) =
      hkRootNumber χ T * (Real.sqrt (t / (modulusNorm m : ℝ)) : ℂ) *
        hkNormalizedG (ψ⁻¹) (hkDualIdeal m I) (t / (modulusNorm m : ℝ) ^ 2) := by
  have hq : 0 < (modulusNorm m : ℝ) := by
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have hD := natAbs_discr_pos K
  have hN := idealNormR_pos K I
  have hβ := heckeBeta_pos K
  let u : ℝ := (idealNormR K I)⁻¹ ^ 2 * heckeBeta K * (1 / t)
  have hu : 0 < u := by dsimp [u]; positivity
  have hA : (4 : ℝ) ^ (2 * nrComplexPlaces K) / u =
      (idealNormR K (hkDualIdeal m I))⁻¹ ^ 2 * heckeBeta K *
        (t / (modulusNorm m : ℝ) ^ 2) := by
    dsimp [u]
    rw [hk_dual_ideal_norm, heckeBeta,
      show 2 * nrComplexPlaces K = nrComplexPlaces K * 2 by omega, pow_mul]
    field_simp
  have hsq : (idealNormR K I)⁻¹ ^ 2 * heckeBeta K =
      ((idealNormR K I)⁻¹ * 2 ^ nrComplexPlaces K /
        Real.sqrt ((discr K).natAbs : ℝ)) ^ 2 := by
    rw [heckeBeta, div_pow, mul_pow, Real.sq_sqrt hD.le, ← pow_mul,
      show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      mul_comm (nrComplexPlaces K) 2, mul_div_assoc]
  have hsqrt : Real.sqrt u =
      ((idealNormR K I)⁻¹ * 2 ^ nrComplexPlaces K /
        Real.sqrt ((discr K).natAbs : ℝ)) * (Real.sqrt t)⁻¹ := by
    dsimp [u]
    rw [Real.sqrt_mul (by positivity), hsq, Real.sqrt_sq (by positivity),
      one_div, Real.sqrt_inv]
  have hpow : (1 / 2 : ℝ) ^ nrComplexPlaces K *
      (2 : ℝ) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  have hcancel : (idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
      Real.sqrt ((discr K).natAbs : ℝ)) * Real.sqrt u = (Real.sqrt t)⁻¹ := by
    rw [hsqrt]
    calc
      _ = (idealNormR K I * (idealNormR K I)⁻¹) *
          ((1 / 2 : ℝ) ^ nrComplexPlaces K * (2 : ℝ) ^ nrComplexPlaces K) *
          (Real.sqrt ((discr K).natAbs : ℝ) /
            Real.sqrt ((discr K).natAbs : ℝ)) * (Real.sqrt t)⁻¹ := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hN.ne', hpow,
          div_self (Real.sqrt_pos.mpr hD).ne']
        ring
  have hden : (modulusNorm m : ℂ) *
      ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
        Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) * (Real.sqrt u : ℂ) =
      (modulusNorm m : ℂ) * (Real.sqrt t : ℂ)⁻¹ := by
    rw [mul_assoc, ← Complex.ofReal_mul, hcancel, Complex.ofReal_inv]
  have hqS : (Real.sqrt (modulusNorm m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have htS : (Real.sqrt t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have hqSq : (Real.sqrt (modulusNorm m : ℝ) : ℂ) ^ 2 = (modulusNorm m : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq.le
  have hcoeff : charValue ψ T.B * hkGaussSum χ T /
      ((modulusNorm m : ℂ) *
        ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
          Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) * (Real.sqrt u : ℂ)) =
      hkRootNumber χ T * (Real.sqrt (t / (modulusNorm m : ℝ)) : ℂ) := by
    rw [hden, hkRootNumber, Real.sqrt_div ht.le, Complex.ofReal_div, ← hqSq]
    field_simp
  change hkWeightedG ψ I u = _
  rw [hk_weighted_unit_box_inversion ψ χ T I hu, hA, hcoeff]
  rfl

end ArtinPrimitiveRoots.Hecke
