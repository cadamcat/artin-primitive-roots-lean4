import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_class_sum_inversion


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField Real
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The conductor-scaled weighted theta functional equation, in the half-weight convention
consumed by the strong Mellin engine. Guide: sol-thin-hk2/PROOFS.md:1440–1476.
Uses hk_weighted_class_sum_inversion; nontriviality removes the q=1 zero-point total in the
Mellin comparison. Every argument here is positive. LEAD. -/
theorem hk_weighted_theta_scalar_FE [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    {t : ℝ} (ht : 0 < t) :
    hkWeightedPhi ψ (1 / t) =
      hkRootNumber χ T * (Real.rpow t ((1 : ℝ) / 2) : ℂ) * hkWeightedPhi (ψ⁻¹) t := by
  have hq : 0 < (modulusNorm m : ℝ) := by
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have harg : (1 / t) / (modulusNorm m : ℝ) =
      1 / ((modulusNorm m : ℝ) * t) := by field_simp
  have hdiv : (modulusNorm m : ℝ) * t / (modulusNorm m : ℝ) = t := by
    field_simp
  have hdivsq : (modulusNorm m : ℝ) * t / (modulusNorm m : ℝ) ^ 2 =
      t / (modulusNorm m : ℝ) := by field_simp
  unfold hkWeightedPhi
  rw [harg, hk_weighted_class_sum_inversion ψ χ T (mul_pos hq ht), hdiv, hdivsq,
    Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow]
  ring

end ArtinPrimitiveRoots.Hecke
