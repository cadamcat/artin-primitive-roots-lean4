import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Choose the uniform finite level and common finite components, decompose each component
into cusps, and restrict all spectral continuations to the same radius at most `1/12`.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:786–796`.
Uses frozen `scalarOf_q`, `exists_classical_components`, `red_decompose`,
`Spec.exists_continuedEisenstein` and proved `Spec.ContinuedEisenstein.exists_restrict`.
Consumed by component reconstruction and frozen `exists_continuedEis`. -/
theorem continuedEis_uniform_level_components {P : CoverPackage D S H A} {G : GlobalDatum P}
    (I : ContinuedEisInput P G) : Nonempty (ContinuedEisComponents I) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
