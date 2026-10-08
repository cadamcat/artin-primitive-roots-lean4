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

/-- Differentiate the actual residue coefficient at a lift with identity exterior components; retain the finite multilinear form for the Weyl-sheet proof.
Guide: sol-thin-thglobal/PROOFS.md:1180–1199.
Uses ThetaNormalizationInput.coefficient, ThetaCommonSections, joint root differentiation under torus integrals and jacquetC_derivative. -/
theorem theta_complex_derivative_tensor {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛)
    (r : P.RP) (hr : ∀ v, v ∉ S.Sf → P.compF v r = 1) :
    thetaFamilyW B L (P.q r) = (thetaNormalizationScalar N)⁻¹ *
      N.Λ (fun v => jacquet (P.loc v.1) A (N.μ v.1)
        (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))) *
      ∏ w, jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6)))) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
