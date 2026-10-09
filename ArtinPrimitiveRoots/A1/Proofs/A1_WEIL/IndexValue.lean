import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance measurableIndexValue (v : FinPlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance borelIndexValue (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- The value at any stabilization cutoff. The cutoff is actual integral data. -/
def LocalGaussianData.stableValue {A : AddCharData F} (W : LocalGaussianData A)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) : ℂ :=
  quadraticIntegral A v (W.measure v) a (W.cutoff v a)

/-- Local regularity required by finite-ball Gaussian arguments. -/
def LocalCharacterRegular (A : AddCharData F) (v : FinPlace F) : Prop :=
  Continuous (A.ψ v) ∧ A.ψ v ≠ 1 ∧ ∀ x, ‖A.ψ v x‖ = 1

/-- Stabilization is an equality of the actual truncated integrals for all later balls. -/
def StabilizesAt (A : AddCharData F) (v : FinPlace F)
    (μ : Measure (v.adicCompletion F)) (a : (v.adicCompletion F)ˣ) (N : ℕ) : Prop :=
  ∀ M, N ≤ M → quadraticIntegral A v μ a M = quadraticIntegral A v μ a N

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
