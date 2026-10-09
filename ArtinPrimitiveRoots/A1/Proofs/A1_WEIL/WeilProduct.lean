import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GlobalSupport
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GlobalReindex
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceDiagonal
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceArch
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.TraceTransfer
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalProduct

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Assemble the global quadratic index product from trace transfer and rational reciprocity.
Guide: PROOFS.md:480–485. Uses: global_index_finite_support; global_index_prime_fibers; quadratic_trace_transfer; quadratic_trace_arch_phase_one; rational_phase_product. -/
theorem weil_product (D : FieldData F) (A : AddCharData F)
    (W : LocalGaussianData A) : ∀ a : Fˣ,
      (Function.mulSupport fun v => W.index v (toLoc v a)).Finite ∧
        ∏ᶠ v, W.index v (toLoc v a) = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
