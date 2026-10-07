import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_scalar_FE
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_hasMellin
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_root_number_norm


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Mellin transport of the scalar theta equation; no Gamma product is evaluated at a pole.
Guide: sol-thin-hk2/PROOFS.md:1477–1511. Uses hk_weighted_theta_scalar_FE,
hk_weighted_theta_hasMellin and the inverse primitive/nontrivial character facts. -/
theorem hk_mellin_FE_completed [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) (s : ℂ) :
    hkCompleted ψ s = hkRootNumber χ T * hkCompleted (ψ⁻¹) (1 - s) := by
  sorry

end ArtinPrimitiveRoots.Hecke
