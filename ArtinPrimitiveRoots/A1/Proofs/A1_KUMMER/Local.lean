import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Types
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ResidueCompatibility

/-! Continuity and unramifiedness of local sextic Hilbert characters. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem kummer_local_continuous (D : FieldData F) (H : HilbertData F)
    (P : FinPlace F) (a : (P.adicCompletion F)ˣ) :
    Continuous (kummerLocal D H P a) := by
  sorry

theorem kummer_local_unit_trivial (D : FieldData F) (H : HilbertData F)
    (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (a : Fˣ)
    (ha : residue P (a : F) ≠ 0) (x : (P.adicCompletion F)ˣ)
    (hx : x ∈ (P.adicCompletionIntegers F).units) :
    kummerLocal D H P (toLoc P a) x = 1 := by
  sorry

theorem kummer_local_eventually_unit_trivial
    (D : FieldData F) (H : HilbertData F) (a : Fˣ) :
    ∀ᶠ P : FinPlace F in Filter.cofinite,
      ∀ x : (P.adicCompletion F)ˣ,
        x ∈ (P.adicCompletionIntegers F).units →
          kummerLocal D H P (toLoc P a) x = 1 := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
