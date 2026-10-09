import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- All explicit rational phases are nonzero units.
Guide: PROOFS.md:482–485. Uses: padicValRat arithmetic; jacobiSym abs bound; dyadic residues. -/
theorem rational_prime_phase_norm (p : Nat.Primes) (a : ℚˣ) :
    ‖rationalPrimePhase p a‖ = 1 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
