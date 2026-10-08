import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.fourierCoeff_subideal_invariant

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Transport a nonzero-frequency residue coefficient to the chosen first coefficient.
Guide: sol-thin-thglobal/PROOFS.md:862–869. Uses adapted-domain existence,
analytic_residue_unique, torusCoeff_analytic, and eisenstein_whittaker.
Feeds the frozen theta_fourierCoeff by definitional identification of the extracted data. -/
theorem theta_fourierCoeff_assembly {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : Fˣ)
    (hPd : FourierAdaptedDomain sec g 𝔞 Pd (ν : F)) :
    torusCoeff P R.theta g Pd (ν : F) =
      fourierFirstCoeff R (P.tc.rat (diagGL ν) * g) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
