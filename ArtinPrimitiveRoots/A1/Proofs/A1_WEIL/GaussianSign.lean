import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNorm

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The index is real of unit modulus because -1 is a local square.
Guide: PROOFS.md:468–475. Uses: local_index_square; local_index_norm; primitive fourth root from D. -/
theorem local_index_sign (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    ((W.index v a : ℂˣ) : ℂ) = 1 ∨ ((W.index v a : ℂˣ) : ℂ) = -1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
