import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_point_ideal_integral


set_option autoImplicit false
open NumberField ClassFieldTheory IsDedekindDomain DedekindResidue
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Principal rescaling preserves the normalized weighted unit-box average.
Guide: sol-thin-hk2/PROOFS.md:1409–1424. Uses hk_point_ideal_integral, weighted Gaussian
reindexing, product formula and the full-unit box retile, as in heckeG_principal_mul. -/
theorem hk_weighted_normalized_class_invariance [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (I J : NumberFieldFractionalIdealGroup K)
    (h : ClassGroup.mk K I = ClassGroup.mk K J) {t : ℝ} (ht : 0 < t) :
    hkNormalizedG ψ I t = hkNormalizedG ψ J t := by
  sorry

end ArtinPrimitiveRoots.Hecke
