import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Continuity, nontriviality, and unit modulus of the frozen local additive character.
Guide: PROOFS.md:464–466. Uses: A.integral; A.trivial_on_F; A.unramified; A1-DUAL; weak approximation. -/
theorem local_character_regular (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) : LocalCharacterRegular A v := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
