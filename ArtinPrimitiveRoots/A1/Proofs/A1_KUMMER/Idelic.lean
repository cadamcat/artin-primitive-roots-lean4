import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Local

/-! Finite Hilbert products and descent to the actual idèle class group. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem kummer_character_exists (D : FieldData F) (H : HilbertData F) (a : Fˣ) :
    ∃ κ : KummerChar F, κ ^ 6 = 1 ∧
      (∀ (w : InfinitePlace F) (x : w.Completionˣ), infiniteComponent κ w x = 1) ∧
      (∀ P : FinPlace F, localComponent κ P = kummerLocal D H P (toLoc P a)) := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
