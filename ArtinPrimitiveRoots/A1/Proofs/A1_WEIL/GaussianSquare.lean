import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Square-class invariance of the normalized quadratic index.
Guide: PROOFS.md:468–470. Uses: stable_value_square_scale; local_absolute_value; positive real rpow. -/
theorem local_index_square (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v (a * b ^ 2) = W.index v a := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
