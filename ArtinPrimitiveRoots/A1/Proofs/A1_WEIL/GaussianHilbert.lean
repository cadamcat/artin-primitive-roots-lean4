import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianBinary
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSign
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Identify the Gaussian multiplicative defect with the quadratic Hilbert symbol.
Guide: PROOFS.md:474–475. Uses: local_index_binary; local_index_sign; local_index_square; H.steinberg; H.nondeg; H.tame; H.product_formula. -/
theorem local_index_hilbert_defect (D : FieldData F) (A : AddCharData F) (H : HilbertData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v a * W.index v b =
      complexRoot D (H.hilb v a b) ^ 3 * W.index v (a * b) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
