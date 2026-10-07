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

/-- A global element that fixes every scalar section fixes the residue Whittaker coefficient.
Uses frozen `eisenstein_automorphic`, `theta_fourierCoeff`, and the defining
Laurent and adapted-lattice conditions; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_tail_invariance {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (k : P.tc.G)
    (hfix : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) :
    ∀ X : P.tc.G, thetaWhit C (X * k) = thetaWhit C X := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
