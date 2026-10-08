import ArtinPrimitiveRoots.Proofs.th_res_whit_b.LambdaCore

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

/-- Descend the residue Whittaker coefficient through the kernel of M(s0), then extend the
resulting linear functional from its range to all local functions by a vector space complement.
Guide: sol-thin-thglobal/PROOFS.md:923–929.
Uses: sectionSpace_family_spanning, analyticFamily_add_smul, ThetaResidueLaws.continuation,
ThetaResidueLaws.dependsOnM, ThetaResidueLaws.linearTranslate, ThetaResidueLaws.fourierCoeff.
Feeds: theta_exterior_whittaker via theta_lambda_whittaker. -/
theorem theta_lambda_descent (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∉ S.Sf) (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    ∃ Λ : ((P.loc v0).L → (G.T v0).V) →ₗ[ℂ] ℂ,
      ∀ (Fam' : AnalyticFamily P G μ) (C' : ContinuedEis Fam'),
        ExteriorFamily Fam v0 Fam' →
          thetaWhit C' g = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0)) := by
  obtain ⟨Λ, θ, hFactor, hFamily⟩ := theta_lambda_descent_core Fam v0 hv0 g laws
  refine ⟨Λ, ?_⟩
  intro Fam' C' hExt
  calc
    thetaWhit C' g = θ ⟨(Fam'.sec (1 / 6)).f v0, (Fam'.sec (1 / 6)).f_sec v0⟩ :=
      hFamily Fam' C' hExt
    _ = Λ (intertwine (P.loc v0) (μ v0) ((Fam'.sec (1 / 6)).f v0)) := (hFactor _).symm

end ArtinPrimitiveRoots.A1.Theta
