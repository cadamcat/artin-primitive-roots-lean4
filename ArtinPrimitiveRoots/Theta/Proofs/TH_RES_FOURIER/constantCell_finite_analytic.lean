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

/-- Both scalar cell sums have one finite delta support for the whole positive half-plane;
every surviving scalar factor is analytic there. This supplies uniform support near 1/6.
Guide: sol-thin-thglobal/PROOFS.md:835–843. Uses intertwine_isSection, sphWeyl,
intertwineC_spherical, and the compact/Alag finite-coset argument. Feeds theta_constantTerm. -/
theorem constantCell_finite_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} {sec : ∀ s : ℂ, GlobalSection P G s}
    {T0 : Finset (FinPlace F)} (hFam : FourierFamilyHyp μ sec T0) (g : P.tc.G) :
    ∃ T : Finset (Fˣ ⧸ G.Δ),
      (∀ s : ℂ, 0 < s.re → ∀ δ : Fˣ ⧸ G.Δ, δ ∉ T →
        scalarOf P G (sec s).f (sec s).fC
          (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0 ∧
        fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g) = 0) ∧
      (∀ δ ∈ T, AnalyticOnNhd ℂ (fun s =>
        scalarOf P G (sec s).f (sec s).fC
          (P.tc.rat (diagGL (Quotient.out δ)) * g)) {s | 0 < s.re}) ∧
      (∀ δ ∈ T, AnalyticOnNhd ℂ (fun s =>
        fourierRawM μ sec s (P.tc.rat (diagGL (Quotient.out δ)) * g)) {s | 0 < s.re}) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
