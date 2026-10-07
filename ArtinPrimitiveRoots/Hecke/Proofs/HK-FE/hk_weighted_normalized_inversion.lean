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
  sorry

end ArtinPrimitiveRoots.Hecke
