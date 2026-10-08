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

/-- Retain S-unipotent equivariance and genuineness of the normalized derivative Whittaker coefficient.
Guide: sol-thin-thglobal/PROOFS.md:1188–1190,1200–1204.
Uses thetaWhit_equiv, thetaFamilyDeriv and differentiation of scalar multiples. -/
theorem theta_WS_fields {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (L : SChar S) (hL : L ∈ 𝓛) :
    (∀ x g, thetaFamilyW B L (P.tc.nS (Multiplicative.ofAdd x) * g) = S.e A x * thetaFamilyW B L g) ∧
    (∀ ζ g, thetaFamilyW B L (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * thetaFamilyW B L g) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
