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

/-- Normalize the differentiated common-section coefficient to the exact T5 indicator and Bessel expression with cS = 4π.
Guide: sol-thin-thglobal/PROOFS.md:1180–1190.
Uses theta_complex_derivative_tensor, theta_normalizationScalar_ne_zero, jacquetC_derivative and CoverPackage.aS_components. -/
theorem theta_complex_derivative_normalization {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛) (y : S.FSˣ) :
    thetaFamilyW B L (P.tc.aS y) =
      (if (y : S.FS).1 ∈ thetaCommonU B then (1 : ℂ) else 0) *
      ∏ w : InfinitePlace F, (Complex.normSq ((y : S.FS).2 w) : ℂ) *
        omegaAng (L.m w) ((y : S.FS).2 w) *
        (besselK (1 / 3) ((4 * Real.pi) * ‖(y : S.FS).2 w‖) : ℂ) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
