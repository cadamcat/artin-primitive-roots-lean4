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

/-- The normalized Jacquet coordinate on the local theta space, including the spherical
vector membership needed to apply uniqueness. No global residue functional is used.
Uses frozen `jacquet_spherical_s0`, `jacquet_linear`, `jacquet_equiv`,
`intertwine_spherical`, and `thetaSpace_le`; feeds `thetaWhit_factor_step`. -/
theorem thetaWhit_local_normalizer (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) (v : FinPlace F) (hv : v ∉ S.Sf) :
    sphWeyl P G v hv (1 / 6) ∈ thetaSpace (P.loc v) (G.T v) (μ v) ∧
      ∃ α : ((P.loc v).L → (G.T v).V) →ₗ[ℂ] ℂ,
        IsWhittakerOn (P.loc v) A (thetaSpace (P.loc v) (G.T v) (μ v)) α ∧
        α (sphWeyl P G v hv (1 / 6)) = 1 ∧
        ∀ k : (P.loc v).L, α (rtr k (sphWeyl P G v hv (1 / 6))) =
          WvAll P G μ v (P.emb v k) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
