import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_eq_ray_character


set_option autoImplicit false
open NumberField ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The conductor-scaled theta's Mellin transform, valid for every complex argument.
Guide: sol-thin-hk2/PROOFS.md:1477–1537. Uses hk_weighted_theta_eq_ray_character,
H1's zero-constant strong FE pair and the positive scaling t/q of the Mellin integral. -/
theorem hk_weighted_theta_hasMellin [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (s : ℂ) :
    HasMellin (hkWeightedPhi ψ) (s / 2) (hkCompleted ψ s) := by
  sorry

end ArtinPrimitiveRoots.Hecke
