import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.WvAll_properties
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_factor_step
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_argument_decomposition
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_tail_invariance

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Iterate the one-place factorization over an exterior support enlargement and convert
the remaining finite product to the frozen dependent finprod.
Uses `WvAll_properties`, `thetaWhit_factor_step`, `thetaWhit_argument_decomposition`,
and `thetaWhit_tail_invariance`; feeds frozen `thetaWhit_factor`. -/
theorem thetaWhit_factor_iteration {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (hT : Fam.T0 = S.Sf)
    (C : ContinuedEis Fam) (ν : Fˣ) (ε : Bool) (gS : P.tc.G) (hgS : gS ∈ P.tc.GS)
    (T : Finset (FinPlace F)) (hT' : ∀ v ∈ T, v ∉ S.Sf) (g : FinPlace F → P.tc.G)
    (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    thetaWhit C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
      thetaWhit C (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, WvAll P G μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
