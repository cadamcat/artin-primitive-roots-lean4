import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_uniform_adapted_lattice
import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_translation_regular_fields
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.RootChartRegularity
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FourierOrbit
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.CompactFourierDomain
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.SpecResidueBounds
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.ResidueReconstruction

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Bound all actual normalized coefficients on a compact set by one summable real majorant; pointwise Summable is insufficient.
Guide: sol-thin-thglobal/PROOFS.md:1211–1224.
Uses theta_uniform_adapted_lattice, uniform mixed derivative bounds on compact coordinate closures and full dual-lattice Fourier decay. -/
theorem theta_compact_fourier_majorant {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (L : SChar S) (hL : L ∈ 𝓛) (K : Set P.tc.G)
    (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ M : Fˣ → ℝ, (∀ ν, 0 ≤ M ν) ∧ Summable M ∧
      ∀ ν g, g ∈ K → ‖thetaFamilyW B L (P.tc.rat (diagGL ν) * g)‖ ≤ M ν := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
