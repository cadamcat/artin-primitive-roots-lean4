import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The normalized ratio at 1 is 1.
Guide: PROOFS.md:468–473. Uses: local_absolute_value; W.integral_ne_zero. -/
theorem local_index_one (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) : W.index v 1 = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
