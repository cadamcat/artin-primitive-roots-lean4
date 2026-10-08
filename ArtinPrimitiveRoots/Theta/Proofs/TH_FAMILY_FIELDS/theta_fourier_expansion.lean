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

/-- Export summability and the exact zero/nonzero-frequency split for the normalized residue.
Guide: sol-thin-thglobal/PROOFS.md:1204–1207.
Uses ThetaTorusFourierInput (supplied by torus_fourier_expansion), theta_constantTerm, theta_fourierCoeff, thetaWhit_nFin argument and mixed root differentiation. -/
theorem theta_fourier_expansion {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P)
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) (g : P.tc.G) :
    Summable (fun ν : Fˣ => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)) ∧
      thetaFamilyTheta B L g = thetaFamilyThetaN B L g +
        ∑' ν : Fˣ, thetaFamilyW B L (P.tc.rat (diagGL ν) * g) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
