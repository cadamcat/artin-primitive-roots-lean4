import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalUnit

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Rational one-dimensional product formula for the explicit local phases.
Guide: PROOFS.md:482–485. Uses: jacobiSym quadratic reciprocity and supplements; rational numerator/denominator factorization. -/
theorem rational_phase_product (a : ℚˣ) :
    (Function.mulSupport fun p : Nat.Primes => rationalPrimePhase p a).Finite ∧
    (∏ᶠ p : Nat.Primes, rationalPrimePhase p a) * rationalArchPhase a = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
