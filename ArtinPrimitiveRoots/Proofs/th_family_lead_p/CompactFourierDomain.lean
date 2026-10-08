import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.theta_uniform_adapted_lattice
import ArtinPrimitiveRoots.Proofs.th_family_lead_p.FourierOrbit

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Extract one compact-uniform adapted Fourier domain, identify dual-frequency coefficients with
the normalized Whittaker values, and prove off-dual vanishing on the compact set. -/
theorem exists_compact_thetaFamily_fourierDomain {P : CoverPackage D S H A}
    (hRP : HasRestrictedProductTopology P) {N : ThetaNormalizationInput P}
    {𝓛 : Finset (SChar S)} (B : ThetaCommonSections P N 𝓛)
    (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛)
    (K : Set P.tc.G) (hK : @IsCompact P.tc.G P.tc.topology K) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume ∧
      Bornology.IsBounded Pd ∧ MeasurableSet Pd ∧
      ∀ g, g ∈ K → ∀ ν : Fˣ,
        ((∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) →
          torusCoeff P (thetaFamilyTheta B L) g Pd (ν : F) =
            thetaFamilyW B L (P.tc.rat (diagGL ν) * g)) ∧
        ((¬ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) →
          thetaFamilyW B L (P.tc.rat (diagGL ν) * g) = 0) := by
  obtain ⟨𝔞, Pd, h𝔞, hPd, hPdBound, hPdMeas, _, hfix, _⟩ :=
    theta_uniform_adapted_lattice hRP B Q K hK
  refine ⟨𝔞, Pd, h𝔞, hPd, hPdBound, hPdMeas, ?_⟩
  intro g hg ν
  constructor
  · intro hν
    exact thetaFamilyW_eq_torusCoeff B Q L g 𝔞 h𝔞 Pd hPd hPdBound hPdMeas
      (hfix g hg) ν hν
  · intro hν
    exact thetaFamilyW_zero_of_not_dual B Q L hL g 𝔞 (hfix g hg) ν hν

end ArtinPrimitiveRoots.A1.Theta
