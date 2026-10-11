import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianScale
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianNorm
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_e.GaussianBinaryHelpers

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Binary Gaussian isometry identity when a+b is nonzero.
Uses: stable_value_square_scale; finite Fubini; determinant-one binary variable change. -/
theorem local_index_binary (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ)
    (h : (a : v.adicCompletion F) + (b : v.adicCompletion F) ≠ 0) :
    W.index v a * W.index v b =
    W.index v (Units.mk0 _ h) * W.index v (a * b / Units.mk0 _ h) := by
  exact ArtinPrimitiveRoots.Proofs.a1_weil_sol_w_e.local_index_binary_actual
    D A W v a b h

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
