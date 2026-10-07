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

/-- Keep the finite component fixed along the left archimedean unipotent orbit and express
the orbit in continuous positive classical coordinates. On closure of a bounded parameter
set the coordinate image is compact and its heights have positive minima.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:812–815`.
Uses `continuedEis_component_representatives`, reconstructed component formulas and
automorphy/level/compact invariance. No analytic
integral argument is included. Consumed by `continuedEis_laurent_torus`. -/
theorem continuedEis_torus_charts {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) : ContinuedEisTorusCharts R := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
