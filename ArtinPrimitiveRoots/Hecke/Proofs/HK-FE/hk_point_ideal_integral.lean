import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory IsDedekindDomain DedekindResidue
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The point ideal is integral, and contraction really recovers it.
Guide: sol-thin-hk2/PROOFS.md:1340–1357. Uses fractional-ideal invertibility and x in I;
no new quotient operation or principality of I is assumed. -/
theorem hk_point_ideal_integral (I : NumberFieldFractionalIdealGroup K) {x : K}
    (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ((hkIntegralPart (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
      (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
  sorry

end ArtinPrimitiveRoots.Hecke
