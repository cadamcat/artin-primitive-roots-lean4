import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianModulus

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Unit modulus of the normalized ratio.
Guide: PROOFS.md:466–470. Uses: stable_quadratic_integral_modulus; W.stable; local_absolute_value. -/
theorem local_index_norm (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : ‖((W.index v a : ℂˣ) : ℂ)‖ = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
