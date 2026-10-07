import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_additive


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Construct the primitive trace character by exact local orders in the codifferent times
inverse conductor. Guide: sol-thin-hk2/PROOFS.md:1261–1306. Uses CRT and Different's trace dual,
and H1's local congruence bridge. Coprimality of B and the ideal equality fix the normalization. -/
theorem hk_primitive_trace_datum [IsTotallyComplex K] (m : RayClassModulus K) :
    Nonempty (HKTraceDatum m) := by
  sorry

end ArtinPrimitiveRoots.Hecke
