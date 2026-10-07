import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_generator


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The exact-order trace generator descends to a primitive additive character. Guide:
sol-thin-hk2/PROOFS.md:1283–1306. Uses hk_primitive_trace_generator, mem_traceDual and the
Fourier-character integral kernel; the annihilator is precisely M. -/
theorem hk_primitive_trace_additive [IsTotallyComplex K] (m : RayClassModulus K)
    (a : Kˣ) (B : Ideal (𝓞 K)) (hB : IsCoprimeTo m B)
    (hB_eq : idealUnit B hB.1 =
      toPrincipalIdeal (𝓞 K) K a * hkModulusUnit m * hkDifferentUnit K) :
    ∃ β : AddChar (HKResidueRing m) ℂ,
      (∀ x : 𝓞 K, β (Ideal.Quotient.mk (modulusIdeal m) x) =
        Real.fourierChar ((Algebra.trace ℚ K ((a : K) * (x : K)) : ℚ) : ℝ)) ∧
      β.IsPrimitive := by
  sorry

end ArtinPrimitiveRoots.Hecke
