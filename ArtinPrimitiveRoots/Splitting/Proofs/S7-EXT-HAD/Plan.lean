import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

def inverseSquareTerms (G : ℂ → ℂ) (z : ℂ) : ℝ :=
  if G z = 0 then (analyticOrderNatAt G z : ℝ) * ‖z‖⁻¹ ^ 2 else 0

def zeroLogTerms (G : ℂ → ℂ) (s z : ℂ) : ℂ :=
  if G z = 0 then (analyticOrderNatAt G z : ℂ) * ((s - z)⁻¹ + z⁻¹) else 0

def genusOneProduct (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∏' z : ℂ, if G z = 0 then
    ((1 - s / z) * Complex.exp (s / z)) ^ analyticOrderNatAt G z else 1

/-- Jensen growth on dyadic disks gives the genus-one convergence exponent. -/
theorem inverse_square_summable (G : ℂ → ℂ) (hG : Differentiable ℂ G) (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    Summable (inverseSquareTerms G) := by
  sorry

/-- Local uniform convergence permits differentiating the genus-one product. -/
theorem genus_one_hasDerivAt (G : ℂ → ℂ) (hG : Differentiable ℂ G) (hG0 : G 0 ≠ 0)
    (hsquare : Summable (inverseSquareTerms G)) (s : ℂ) (hs : G s ≠ 0) :
    Summable (zeroLogTerms G s) ∧
      HasDerivAt (genusOneProduct G)
        (genusOneProduct G s * ∑' z : ℂ, zeroLogTerms G s z) s := by
  sorry

/-- Growth forces the zero-free quotient to be the exponential of an affine function. -/
theorem genus_one_affine_factorization (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hG0 : G 0 ≠ 0) (hsquare : Summable (inverseSquareTerms G))
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ A B : ℂ, ∀ s : ℂ, G s = Complex.exp (A + B * s) * genusOneProduct G s := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
