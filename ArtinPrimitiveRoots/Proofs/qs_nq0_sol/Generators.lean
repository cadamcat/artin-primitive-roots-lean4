import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Foundation

/-!
# Fixed choices for the canonical narrow family

The supplied primitive twelfth root and a complex embedding give the field
data used to read A1's root-of-unity-valued symbols.
-/

set_option autoImplicit false

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Supply A1's field data for an arbitrary number field containing a twelfth root. -/
theorem qs_nq0_field_data (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12) :
    Nonempty (ArtinPrimitiveRoots.A1.FieldData K) := by
  obtain ⟨ζ, hζ⟩ := hμ
  obtain ⟨σ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  exact ⟨⟨ζ, hζ, σ⟩⟩

end ArtinPrimitiveRoots.A2
