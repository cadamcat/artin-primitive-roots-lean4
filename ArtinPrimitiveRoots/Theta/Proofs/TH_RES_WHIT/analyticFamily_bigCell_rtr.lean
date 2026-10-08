import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- Insert a place and replace its section by a translated compactly supported big-cell
family, preserving all other sections. This supplies the M/J analyticity and uniform level
needed by family spanning and residue coordinates.
Guide: sol-thin-thglobal/PROOFS.md:915–922,1007–1010.
Uses: bigCell_isSection, intertwine_bigCell_analytic, jacquet_stable, IsSection.rtr.
Feeds: sectionSpace_family_spanning and thetaWhit_section_multilinear. -/
theorem analyticFamily_bigCell_rtr (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (φ : v0.adicCompletion F → (G.T v0).V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (h : (P.loc v0).L) :
    ∃ Fam' : AnalyticFamily P G μ, ExteriorFamily Fam v0 Fam' ∧
      ∀ s, (Fam'.sec s).f v0 = rtr h (bigCell (P.loc v0) (G.T v0) s φ) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
