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

/-- Convert the single compact majorant and the exact Fourier identity into the consumer finite-tail estimate, in the cover topology.
Guide: sol-thin-thglobal/PROOFS.md:1211–1224.
Uses theta_compact_fourier_majorant and the supplied theta_fourier_expansion conclusion. -/
theorem theta_fourierLocallyUniform {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛)
    (hFourier : ∀ g, Summable (fun ν : Fˣ => thetaFamilyW B L (P.tc.rat (diagGL ν) * g)) ∧
      thetaFamilyTheta B L g = thetaFamilyThetaN B L g +
        ∑' ν : Fˣ, thetaFamilyW B L (P.tc.rat (diagGL ν) * g))
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F₀ : Finset Fˣ, ∀ F' : Finset Fˣ, F₀ ⊆ F' → ∀ g ∈ K,
      ‖thetaFamilyTheta B L g - thetaFamilyThetaN B L g -
        ∑ ν ∈ F', thetaFamilyW B L (P.tc.rat (diagGL ν) * g)‖ < ε := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
