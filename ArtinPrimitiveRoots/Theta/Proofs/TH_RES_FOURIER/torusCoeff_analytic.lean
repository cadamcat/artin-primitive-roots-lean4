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

/-- The continued torus integral is analytic on a possibly smaller continuation domain.
The radius is chosen after g and Pd; pointwise E_analytic alone is not an integration theorem.
Guide: sol-thin-thglobal/PROOFS.md:835–848, 862–882; the compact Banach argument is at 811–822.
Uses red_decompose, P-SPEC compact-valued continuation, and analytic uniqueness.
Feeds theta_constantTerm and analytic_residue_unique applications in Fourier assembly. -/
theorem torusCoeff_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : FourierIdealFix sec g 𝔞) (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hb : Bornology.IsBounded Pd) (hm : MeasurableSet Pd) (ν : F) :
    ∃ η : ℝ, 0 < η ∧ η ≤ R.ε ∧ η ≤ (1 / 6 : ℝ) ∧
      AnalyticOnNhd ℂ (fun s => torusCoeff P (R.E s) g Pd ν)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) η) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
