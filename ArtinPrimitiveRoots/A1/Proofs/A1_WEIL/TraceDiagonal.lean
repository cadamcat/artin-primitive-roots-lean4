import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Diagonalize the genuine nondegenerate rational trace form.
Guide: PROOFS.md:480–481. Uses: traceForm_nondegenerate; equivalent_weightedSumSquares_units_of_nondegenerate. -/
theorem quadratic_trace_diagonal_exists (a : Fˣ) : Nonempty (QuadraticTraceDiagonal a) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
