import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_gauss_sum


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The different-normalized root number has norm one, including conductor norm one.
Guide: sol-thin-hk2/PROOFS.md:1321–1338. Uses hk_primitive_trace_gauss_sum,
finite ray-character unitarity and T.coprime. -/
theorem hk_root_number_norm [IsTotallyComplex K] {m : RayClassModulus K}
    {ψ : RayClassGroup m →* ℂˣ} (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) :
    ‖hkRootNumber χ T‖ = 1 := by
  sorry

end ArtinPrimitiveRoots.Hecke
