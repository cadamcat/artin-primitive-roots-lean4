import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Foundation
import ArtinPrimitiveRoots.A1.Hilbert

/-!
# Fixed choices for the canonical narrow family

The supplied primitive twelfth root and a complex embedding give the field
data used to read A1's root-of-unity-valued symbols. A1's allowed-generator
producer gives one fixed generator for every exterior ideal.
-/

set_option autoImplicit false

open scoped NumberField

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Supply A1's field data for an arbitrary number field containing a twelfth root. -/
theorem qs_nq0_field_data (hμ : ∃ ζ : K, IsPrimitiveRoot ζ 12) :
    Nonempty (ArtinPrimitiveRoots.A1.FieldData K) := by
  obtain ⟨ζ, hζ⟩ := hμ
  obtain ⟨σ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  exact ⟨⟨ζ, hζ, σ⟩⟩

variable {CE : ℕ} {condη : Ideal (𝓞 K)}

/-- Fix allowed generators on the exterior ideals, extending the choice by `1` elsewhere. -/
theorem qs_nq0_allowed_generators (Sd : ArtinPrimitiveRoots.A1.SData K CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData K) (Bd : ArtinPrimitiveRoots.A1.BData Sd H) :
    ∃ a : Ideal (𝓞 K) → Kˣ, ∀ I, Sd.IsExterior I →
      Sd.IsGen (a I : K) I ∧ Bd.Allowed (a I) := by
  classical
  let a : Ideal (𝓞 K) → Kˣ := fun I =>
    if hI : Sd.IsExterior I then (Bd.exists_allowed I hI).choose else 1
  refine ⟨a, ?_⟩
  intro I hI
  simpa only [a, dif_pos hI] using (Bd.exists_allowed I hI).choose_spec

end ArtinPrimitiveRoots.A2
