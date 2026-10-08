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

/-- Form a local affine linear combination of two families with the same exterior sections.
The resulting family has the same inserted support and a common small level.
Guide: sol-thin-thglobal/PROOFS.md:915–929.
Uses: sectionSpace closure, intertwine_isSection (integrability), jacquet_linear.
Feeds: theta_lambda_descent and thetaWhit_section_multilinear. -/
theorem analyticFamily_add_smul (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (Fam₁ Fam₂ : AnalyticFamily P G μ) (h₁ : ExteriorFamily Fam v0 Fam₁)
    (h₂ : ExteriorFamily Fam v0 Fam₂) (c : ℂ) :
    ∃ Fam₃ : AnalyticFamily P G μ, ExteriorFamily Fam v0 Fam₃ ∧
      ∀ s, (Fam₃.sec s).f v0 = (Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0 := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
