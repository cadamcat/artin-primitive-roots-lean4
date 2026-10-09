import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Change the variable in stabilized integrals by multiplication by a local unit.
Guide: PROOFS.md:468–470. Uses: local_haar_scale; local_character_regular; W.stable. -/
theorem stable_value_square_scale (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.stableValue v (a * b ^ 2) =
      (absFin v (b : v.adicCompletion F) : ℂ)⁻¹ * W.stableValue v a := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
