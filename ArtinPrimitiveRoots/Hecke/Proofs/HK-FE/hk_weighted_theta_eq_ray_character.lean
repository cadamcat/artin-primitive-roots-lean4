import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_class_invariance


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The weighted ordinary-class sum is H1's ray-character sum. Orthogonality also removes
the zero point at the unit modulus. Guide: sol-thin-hk2/PROOFS.md:1340–1370,1512–1537;
sol-thin-hk1/PROOFS.md:1021–1067. Uses H1's ray ideal parametrization, weighted unit-box
unfolding and hk_point_ideal_integral; no primitive FE assumption is needed. -/
theorem hk_weighted_theta_eq_ray_character [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) {t : ℝ} (ht : 0 < t) :
    hkWeightedH ψ t = (rayCharacterFEPair (hkRayRepresentatives m) ψ).f t := by
  sorry

end ArtinPrimitiveRoots.Hecke
