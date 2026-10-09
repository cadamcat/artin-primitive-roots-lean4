import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.mem_span_idealArchBasis
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.archimedean_trace_sum
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- The rational frequency corresponding to an integer Fourier index.
The sign accounts for the negative exponential in the theta character. -/
def idealTraceFrequency (n : Module.Free.ChooseBasisIndex ℤ I → ℤ) : F := by
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ I)
  exact -(∑ i, (n i : ℚ) • (NumberField.basisOfFractionalIdeal F I).traceDual i)

/-- Pairing a trace-dual frequency with an archimedean ideal basis
vector recovers the corresponding integer coordinate with a minus sign. -/
theorem idealTraceFrequency_pairing (n : Module.Free.ChooseBasisIndex ℤ I → ℤ)
    (j : Module.Free.ChooseBasisIndex ℤ I) :
    (2 : ℝ) * ∑ w : InfinitePlace F,
      ((w.embedding (idealTraceFrequency F I n)) * (idealArchBasis F I j w)).re =
        -(n j : ℝ) := by
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℤ I)
  let b := NumberField.basisOfFractionalIdeal F I
  have htrace : Algebra.trace ℚ F (idealTraceFrequency F I n * b j) = -(n j : ℚ) := by
    simp [idealTraceFrequency, b, Finset.sum_mul, smul_mul_assoc]
  have hb : idealArchBasis F I j =
      (fun w : InfinitePlace F => w.embedding (b j)) := by
    change totallyComplexMixedEquiv F
      (NumberField.mixedEmbedding.fractionalIdealLatticeBasis F I j) = _
    rw [NumberField.mixedEmbedding.fractionalIdealLatticeBasis_apply]
    exact totallyComplexMixedEquiv_embedding F (b j)
  have harch := congrArg Complex.re
    (archimedean_trace_sum F (idealTraceFrequency F I n * b j))
  rw [htrace] at harch
  simpa [hb, map_mul] using harch.symm

end ArtinPrimitiveRoots.A1.Theta
