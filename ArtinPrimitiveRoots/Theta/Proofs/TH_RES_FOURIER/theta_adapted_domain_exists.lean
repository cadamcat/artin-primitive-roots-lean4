import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- An adapted nonzero ideal and a bounded measurable domain exist at every g,
uniformly over the family parameter. Guide: sol-thin-thglobal/PROOFS.md:851–855.
Uses FourierFamilyHyp.level, restricted-product support, inverse different, and ideal lattices.
Feeds theta_fourierCoeff and thetaWhit_equiv through fourierFirstCoeff. -/
theorem theta_adapted_domain_exists {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (g : P.tc.G) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)),
      FourierAdaptedDomain sec g 𝔞 Pd 1 ∧ MeasurableSet Pd := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
