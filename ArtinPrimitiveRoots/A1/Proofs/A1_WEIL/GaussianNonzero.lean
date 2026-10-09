import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianNonzero (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianNonzero (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The stabilized one-dimensional Gaussian integral is nonzero.
Guide: PROOFS.md:466–468. Uses: local_haar_scale; LocalCharacterRegular; finite coset orthogonality. -/
theorem stable_quadratic_integral_ne_zero (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N : ℕ) (hN : StabilizesAt A v μ a N) :
    quadraticIntegral A v μ a N ≠ 0 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
