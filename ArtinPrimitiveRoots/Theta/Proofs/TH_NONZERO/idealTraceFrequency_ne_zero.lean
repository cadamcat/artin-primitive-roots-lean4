import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.idealTraceFrequency_pairing

set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]
variable (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)

/-- A nonzero integer Fourier index gives a nonzero rational frequency. -/
theorem idealTraceFrequency_ne_zero {n : Module.Free.ChooseBasisIndex ℤ I → ℤ}
    (hn : n ≠ 0) : idealTraceFrequency F I n ≠ 0 := by
  intro hfreq
  apply hn
  funext j
  have hj : (n j : ℝ) = 0 := by
    simpa [hfreq] using (idealTraceFrequency_pairing F I n j).symm
  exact_mod_cast hj

end ArtinPrimitiveRoots.A1.Theta
