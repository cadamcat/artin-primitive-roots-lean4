import ArtinPrimitiveRoots.Theta.Assemble

/-!
# A1 theta consumer interface

The theorem lives after the assembled theta construction to avoid the import cycle between
`A1.ThetaInterface` and `Theta.Assemble`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 8. The cubic theta input: consumer form `th:theta-interface` (T1–T7) -/

/-- **th:theta-interface.** The cover is fixed before the S-characters; for every finite family of
admissible S-characters there is a theta family. Route C packages P-COVER, P-LOCAL, P-EIS,
P-SPEC, P-RES, P-ASSEMBLE (A1-DESIGN §3).
Corrected per rev-theta through the regularity fields of `ThetaFamily`; C10/C11 of
`sol-gate-theta` fix the restricted-product topology and joint root smoothness; C2 exposes the
compatible `CoverPackage`. -/
theorem theta_interface (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (A : AddCharData F) :
    ∃ P : ArtinPrimitiveRoots.A1.Theta.CoverPackage D S H A,
      ∀ 𝓛 : Finset (SChar S), Nonempty (ThetaFamily P.tc 𝓛) := by
  apply ArtinPrimitiveRoots.A1.Theta.theta_interface_of_steinberg D S H A
  intro v a h
  exact H.steinberg v a h

end ArtinPrimitiveRoots.A1
