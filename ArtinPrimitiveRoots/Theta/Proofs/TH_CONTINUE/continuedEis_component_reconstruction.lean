import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_unique
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Extend the finite component cusp sums and their residues to adelic functions. The same
point representation transports both sums and the original series, and the reconstructed
functions have rational automorphy, finite-level invariance and infinite-compact invariance.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–808`.
Uses `continuedEis_component_unique`, `continuedEis_component_representatives`,
frozen `eisenstein_automorphic`, `scalarOf_q`,
and the component data supplied by `continuedEis_uniform_level_components`.
Consumed by series/analytic, torus-chart, smoothness parts and `exists_continuedEis`. -/
theorem continuedEis_component_reconstruction {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) :
    Nonempty (ContinuedEisReconstruction C) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
