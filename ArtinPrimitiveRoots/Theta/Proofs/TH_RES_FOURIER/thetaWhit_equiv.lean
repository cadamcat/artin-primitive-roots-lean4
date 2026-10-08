import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_fourierCoeff

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Genuineness and the exact S and exterior unipotent character laws for the chosen
first residue coefficient. Guide: sol-thin-thglobal/PROOFS.md:872–882.
Uses adapted-domain existence, analytic_residue_unique, torusCoeff_analytic, whittakerE_equiv.
Feeds the frozen thetaWhit_equiv; no rationality assumption is made on S-unipotents. -/
theorem thetaWhit_equiv_assembly {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0)
    (R : FourierResidueData sec) :
    (∀ ζ g, fourierFirstCoeff R (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * fourierFirstCoeff R g) ∧
    (∀ x g, fourierFirstCoeff R (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * fourierFirstCoeff R g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, fourierFirstCoeff R (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * fourierFirstCoeff R g) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
