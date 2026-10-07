import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Realize the global coefficient with one exterior argument as a Whittaker functional
on the translated Weyl spherical vector. Its scaling absorbs `cv v (1/6)`.
Uses frozen `theta_exterior_whittaker`, `theta_linear_translate`,
`intertwine_rtr`, `intertwine_spherical`, and continuation uniqueness;
feeds `thetaWhit_factor_step`. The original family has exterior level exactly S. -/
theorem thetaWhit_factor_functional {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (C : ContinuedEis Fam) (v : FinPlace F) (hv : v ∉ S.Sf)
    (X : P.tc.G) (hX : ∀ k : (P.loc v).L, X * P.emb v k = P.emb v k * X) :
    ∃ Λ : ((P.loc v).L → (G.T v).V) →ₗ[ℂ] ℂ,
      IsWhittakerOn (P.loc v) A (thetaSpace (P.loc v) (G.T v) (μ v)) Λ ∧
      ∀ k : (P.loc v).L, thetaWhit C (X * P.emb v k) =
        Λ (rtr k (sphWeyl P G v hv (1 / 6))) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
