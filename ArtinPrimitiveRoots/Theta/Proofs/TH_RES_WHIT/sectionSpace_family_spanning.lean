import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_bigCell_rtr

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

/-- Every local section at s0 is a finite linear combination of s0 values of analytic global
families with that place inserted and the exterior sections held fixed. Translated big-cell
families first match the value at 1; section_eq_bigCell supplies the remaining section.
Guide: sol-thin-thglobal/PROOFS.md:915–922.
Uses: analyticFamily_bigCell_rtr, section_eq_bigCell, bigCell_apply and compact open local balls.
Feeds: theta_lambda_descent, theta_lambda_whittaker, thetaWhit_section_multilinear. -/
theorem sectionSpace_family_spanning (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (f : (P.loc v0).L → (G.T v0).V)
    (hf : f ∈ sectionSpace (P.loc v0) (G.T v0) (1 / 6)) :
    ∃ n : ℕ, ∃ c : Fin n → ℂ, ∃ fams : Fin n → AnalyticFamily P G μ,
      (∀ i, ExteriorFamily Fam v0 (fams i)) ∧
      f = ∑ i, c i • (((fams i).sec (1 / 6)).f v0) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
