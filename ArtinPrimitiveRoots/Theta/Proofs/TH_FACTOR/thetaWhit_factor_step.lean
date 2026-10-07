import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_factor_functional
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_local_normalizer

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- One-place factorization, valid even when the coefficient at X vanishes.
Uses `thetaWhit_factor_functional`, `thetaWhit_local_normalizer`, and frozen
`whittaker_theta_dim_le_one`/`thetaSpace_le`; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_factor_step {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (C : ContinuedEis Fam) (v : FinPlace F) (hv : v ∉ S.Sf)
    (X : P.tc.G) (hX : ∀ k : (P.loc v).L, X * P.emb v k = P.emb v k * X)
    (k : (P.loc v).L) :
    thetaWhit C (X * P.emb v k) = thetaWhit C X * WvAll P G μ v (P.emb v k) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
