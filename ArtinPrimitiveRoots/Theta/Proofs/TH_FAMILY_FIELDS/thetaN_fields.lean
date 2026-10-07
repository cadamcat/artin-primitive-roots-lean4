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

/-- Export the constant-term invariances, torus continuity and T7 radiality for the same normalized constant term.
Guide: sol-thin-thglobal/PROOFS.md:1200–1210.
Uses thetaFamilyBaseN, theta_constantTerm, intertwineC_spherical and left-translation commutation with thetaFamilyDeriv. -/
theorem thetaN_fields {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ (b : GL (Fin 2) F), (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      ∀ g, thetaFamilyThetaN B L (P.tc.rat b * g) = thetaFamilyThetaN B L g) ∧
    (∀ g, ∀ k ∈ P.tc.Kext, thetaFamilyThetaN B L (g * k) = thetaFamilyThetaN B L g) ∧
    (∀ ζ g, thetaFamilyThetaN B L (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyThetaN B L g) ∧
    (∀ g h, Continuous fun y : S.FSˣ => thetaFamilyThetaN B L (g * P.tc.aS y * h)) ∧
    (∀ (w : InfinitePlace F) (zc : ℂˣ), ‖(zc : ℂ)‖ = 1 →
      ∀ g, thetaFamilyThetaN B L (P.tc.aS (S.atComplex w zc) * g) = thetaFamilyThetaN B L g) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
