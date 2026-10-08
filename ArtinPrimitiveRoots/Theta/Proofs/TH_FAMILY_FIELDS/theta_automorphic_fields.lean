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

/-- Scale the three frozen derivative-action laws to the normalized theta function.
Guide: sol-thin-thglobal/PROOFS.md:1200–1204.
Uses ThetaDerivativeAction (supplied by frozen Rderiv_spec in Assemble) and thetaFamilyTheta. -/
theorem theta_automorphic_fields {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (hAction : ThetaDerivativeAction B)
    (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ ζ g, thetaFamilyTheta B L (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyTheta B L g) ∧
    (∀ γ g, thetaFamilyTheta B L (P.tc.rat γ * g) = thetaFamilyTheta B L g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, thetaFamilyTheta B L (g * k) = thetaFamilyTheta B L g) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
