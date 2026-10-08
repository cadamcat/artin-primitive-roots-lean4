import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Local

/-! Positive tame orientation at the frozen global uniformizer. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem frobenius_residue_root (D : FieldData F) (H : HilbertData F)
    (a : Fˣ) (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal)
    (ha : residue P (a : F) ≠ 0) :
    ((kummerLocal D H P (toLoc P a) (toLoc P (uniformizerUnit P)) : ℂˣ) : ℂ) =
      chi D P (a : F) := by
  sorry

theorem kummer_prime_values (D : FieldData F) (H : HilbertData F) (a : Fˣ)
    (κ : KummerChar F)
    (hloc : ∀ P : FinPlace F, localComponent κ P = kummerLocal D H P (toLoc P a))
    (P : FinPlace F) (h6 : (6 : 𝓞 F) ∉ P.asIdeal) (ha : residue P (a : F) ≠ 0) :
    unramifiedAt κ P ∧ primeValue κ P = chi D P (a : F) := by
  sorry

end ArtinPrimitiveRoots.A1.KummerProofs
