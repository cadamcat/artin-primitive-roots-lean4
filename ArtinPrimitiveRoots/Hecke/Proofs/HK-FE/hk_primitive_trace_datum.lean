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
  obtain ⟨a, B, hB, hB_eq⟩ := hk_primitive_trace_generator m
  obtain ⟨β, hβ_val, hβ_prim⟩ := hk_primitive_trace_additive m a B hB hB_eq
  exact ⟨⟨a, B, hB, hB_eq, β, hβ_val, hβ_prim⟩⟩

end ArtinPrimitiveRoots.Hecke
