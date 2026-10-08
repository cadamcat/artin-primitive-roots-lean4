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

/-- Choose one nonzero period ideal and bounded measurable fundamental domain for all points of a compact set in the canonical restricted-product quotient.
Guide: sol-thin-thglobal/PROOFS.md:1211–1224.
Uses HasRestrictedProductTopology, CoverPackage.q_quotient, uniform common-family finite level and finite compact chart covers. -/
theorem theta_uniform_adapted_lattice {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B)
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume ∧
      Bornology.IsBounded Pd ∧ MeasurableSet Pd ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1) ∧
      (∀ g ∈ K, ∀ s, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P N.G (B.Fam.sec s).f (B.Fam.sec s).fC h) ∧
      (∀ L ∈ 𝓛, ∀ g ∈ K, ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x,
        thetaFamilyTheta B L (nInf P (x + infEmbA ξ) * g) =
          thetaFamilyTheta B L (nInf P x * g)) := by
  sorry
end ArtinPrimitiveRoots.A1.Theta
