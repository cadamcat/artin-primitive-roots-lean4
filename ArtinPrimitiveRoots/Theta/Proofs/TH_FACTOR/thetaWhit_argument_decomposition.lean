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

/-- Decompose the frozen factorization argument using the exact Finset.toList order.
The tail is also certified to fix the scalar sections of the given family; arbitrary
Kext membership alone is not used to assert this.
Uses frozen `rat_diag`, `rat_weyl`, `aExt_split`, `wExt_split`, cover component
laws, `scalarOf_q`, and exterior sphericity; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_argument_decomposition {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (ν : Fˣ) (ε : Bool) (gS : P.tc.G) (hgS : gS ∈ P.tc.GS)
    (T U : Finset (FinPlace F)) (hTU : T ⊆ U) (hU : ∀ v ∈ U, v ∉ S.Sf)
    (hν : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ U →
      residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0)
    (g : FinPlace F → P.tc.G) (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    ∃ k ∈ P.tc.Kext, (∀ v ∈ U, ∀ h ∈ P.tc.Gloc v, k * h = h * k) ∧
      P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS *
        (T.toList.map g).prod =
      (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (U.toList.map (thetaWhit_localArgument P ν ε T g)).prod * k ∧
      ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
