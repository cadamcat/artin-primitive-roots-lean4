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

/-- Translate one already inserted local section of an analytic family. The support and
exterior sections are fixed; conjugating a common small level gives a common translated level.
Guide: sol-thin-thglobal/PROOFS.md:923–934 (translation step).
Uses: IsSection.rtr, intertwine_rtr, the family's J_analytic and level fields.
Feeds: theta_lambda_whittaker. -/
theorem analyticFamily_rtr (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∈ Fam.T0) (h : (P.loc v0).L) :
    ∃ Fam' : AnalyticFamily P G μ, Fam'.T0 = Fam.T0 ∧
      (∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) ∧
      ∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
