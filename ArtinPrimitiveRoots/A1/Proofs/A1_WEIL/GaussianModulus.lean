import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.HaarScale

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableGaussianModulus (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelGaussianModulus (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The ratio modulus with arbitrary Haar normalization; all constants cancel against I(1).
Guide: PROOFS.md:466–468. Uses: local_haar_scale; finite Fubini; character orthogonality. -/
theorem stable_quadratic_integral_modulus (A : AddCharData F) (v : FinPlace F) (μ : Measure (v.adicCompletion F))
    (hμ : Measure.IsAddHaarMeasure μ) (hψ : LocalCharacterRegular A v)
    (a : (v.adicCompletion F)ˣ) (N M : ℕ)
    (hN : StabilizesAt A v μ a N) (hM : StabilizesAt A v μ 1 M) :
    absFin v (a : v.adicCompletion F) * ‖quadraticIntegral A v μ a N‖ ^ 2 =
      ‖quadraticIntegral A v μ 1 M‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
