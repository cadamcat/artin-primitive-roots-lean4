import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Bound the global index support by bad places and the divisor of a.
Guide: PROOFS.md:480–481. Uses: exterior_local_index_unit; SData.nonempty; finite fractional-ideal factorization. -/
theorem global_index_finite_support (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A) (a : Fˣ) :
    (Function.mulSupport fun v => W.index v (toLoc v a)).Finite := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
