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

/-- Differentiate the frozen base factorization through commuting exterior translators and preserve its exact finite and finite-support products.
Guide: sol-thin-thglobal/PROOFS.md:1188–1190,1133–1162.
Uses ThetaBaseFactorization (supplied by thetaWhit_factor), thetaFamilyDeriv and CoverPackage.comm_S. -/
theorem theta_family_factor {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (hFactor : ThetaBaseFactorization B)
    (L : SChar S) (hL : L ∈ 𝓛) (ν : Fˣ) (ε : Bool) (gS : P.tc.G)
    (hgS : gS ∈ P.tc.GS) (T : Finset (FinPlace F)) (hT : ∀ v ∈ T, v ∉ S.Sf)
    (g : FinPlace F → P.tc.G) (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    thetaFamilyW B L (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaFamilyW B L (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), thetaExteriorWv P N.G N.μ v (P.tc.a v (toLoc v ν)) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
