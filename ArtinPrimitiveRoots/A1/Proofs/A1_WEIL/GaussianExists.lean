import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalHaar
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianStabilization
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNonzero

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Assemble measures, actual stabilization cutoffs, and nonzero normalized ratios.
Guide: PROOFS.md:464–469. Uses: local_haar_exists; local_character_regular; quadratic_integral_stabilizes; stable_quadratic_integral_ne_zero; local_absolute_value. -/
theorem local_gaussian_data (D : FieldData F) (A : AddCharData F) :
    Nonempty (LocalGaussianData A) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
