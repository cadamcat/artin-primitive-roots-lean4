import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_inversion
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_class_invariance


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Sum normalized ideal theta over ordinary classes, using the actual dual-class permutation.
Guide: sol-thin-hk2/PROOFS.md:1405–1450. Uses hk_weighted_normalized_inversion,
hk_weighted_normalized_class_invariance and classRep. LEAD. -/
theorem hk_weighted_class_sum_inversion [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    {t : ℝ} (ht : 0 < t) :
    hkWeightedH ψ (1 / t) =
      hkRootNumber χ T * (Real.sqrt (t / (modulusNorm m : ℝ)) : ℂ) *
        hkWeightedH (ψ⁻¹) (t / (modulusNorm m : ℝ) ^ 2) := by
  sorry

end ArtinPrimitiveRoots.Hecke
