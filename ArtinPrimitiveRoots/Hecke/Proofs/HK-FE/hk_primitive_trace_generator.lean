import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- CRT generator of the inverse conductor times codifferent, with exact conductor-prime
orders recorded by coprimality of B. Guide: sol-thin-hk2/PROOFS.md:1261–1281.
Uses CRT in an invertible ideal after clearing one denominator; neither M nor the different
is assumed principal. -/
theorem hk_primitive_trace_generator [IsTotallyComplex K] (m : RayClassModulus K) :
    ∃ (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B),
      idealUnit B hB.1 = toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K := by
  sorry

end ArtinPrimitiveRoots.Hecke
