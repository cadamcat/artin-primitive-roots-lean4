import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalAbsolute

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianStabilization (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianStabilization (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- Stabilize the actual ball integral by cancelling all sufficiently remote shells.
Guide: PROOFS.md:464–466. Uses: A.integral; LocalCharacterRegular; valuation balls; Haar translation. -/
theorem quadratic_integral_stabilizes (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) : ∃ N, StabilizesAt A v μ a N := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
