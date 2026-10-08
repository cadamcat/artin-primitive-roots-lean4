import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.torusCoeff_analytic
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.analytic_residue_unique
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.adapted_domain_measurable_representative

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Normalized nonzero-frequency residue coefficients agree on an adapted ideal and any
nonzero subideal, including different bounded null-measurable domain choices.
Guide: sol-thin-thglobal/PROOFS.md:855–861. Uses torusCoeff_analytic,
analytic_residue_unique, and eisenstein_whittaker. Feeds the choice independence in thetaWhit. -/
theorem fourierCoeff_subideal_invariant {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (hsub : 𝔟 ≤ 𝔞)
    (Pd Qd : Set (InfinitePlace F → ℂ)) (ν : Fˣ)
    (hPd : FourierAdaptedDomain sec g 𝔞 Pd (ν : F))
    (hQd : FourierAdaptedDomain sec g 𝔟 Qd (ν : F)) :
    torusCoeff P R.theta g Pd (ν : F) = torusCoeff P R.theta g Qd (ν : F) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
