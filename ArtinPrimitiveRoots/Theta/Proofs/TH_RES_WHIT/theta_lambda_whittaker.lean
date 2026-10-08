import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.sectionSpace_family_spanning
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_rtr

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

/-- A descended residue functional is Whittaker on the theta space. Translate generators,
commute the local root past g, apply residue equivariance, and extend by span induction.
Guide: sol-thin-thglobal/PROOFS.md:929–934.
Uses: sectionSpace_family_spanning, analyticFamily_rtr, intertwine_rtr,
ThetaResidueLaws.linearTranslate, ThetaResidueLaws.fourierCoeff, ThetaResidueLaws.equiv, CoverPackage.emb_n.
Feeds: theta_exterior_whittaker. -/
theorem theta_lambda_whittaker (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G)
    (hg : ∀ h : (P.loc v0).L, g * P.emb v0 h = P.emb v0 h * g)
    (laws : ThetaResidueLaws P G μ)
    (Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ)
    (hΛ : ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
      ExteriorFamily Fam v0 Fam' →
        thetaWhit C' g = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0))) :
    IsWhittakerOn (P.loc v0) A (thetaSpace (P.loc v0) (G.T v0) (μ v0)) Λ := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
