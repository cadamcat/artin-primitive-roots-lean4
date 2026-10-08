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

/-- Replace a bounded null-measurable fundamental domain by a bounded measurable one a.e.
Guide: sol-thin-thglobal/PROOFS.md:846–848. Uses IsAddFundamentalDomain.nullMeasurableSet.
Feeds torusCoeff_analytic and all three frozen residue Fourier declarations. -/
theorem adapted_domain_measurable_representative
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) :
    ∃ Q : Set (InfinitePlace F → ℂ), MeasurableSet Q ∧ Bornology.IsBounded Q ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Q volume ∧
      Q =ᵐ[volume] Pd := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
