import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Choose the actual global datum, Haar measures and a nonzero multilinear evaluation.
Guide: sol-thin-thglobal/PROOFS.md:1165–1172.
Uses exists_globalDatum, LocHaar.nonempty, exists_theta_ne_zero, thetaWhit_ne_zero thetaWhit_multilinear and the supplied thetaWhit_factor conclusion. -/
theorem theta_normalization_input (P : CoverPackage D S H A)
    (hSt : ∀ v, SteinbergAt H v) (hFactor : ThetaFactorizationInput P) : Nonempty (ThetaNormalizationInput P) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
