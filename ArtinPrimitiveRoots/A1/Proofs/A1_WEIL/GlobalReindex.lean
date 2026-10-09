import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Regroup a finite-support global product by its unique rational residue prime.
Guide: PROOFS.md:480–481. Uses: finite residue fields; rational-prime fibers; finprod partition identities. -/
theorem global_index_prime_fibers (A : AddCharData F) (W : LocalGaussianData A) (a : Fˣ)
    (ha : (Function.mulSupport fun v => W.index v (toLoc v a)).Finite) :
    (∏ᶠ v : FinPlace F, ((W.index v (toLoc v a) : ℂˣ) : ℂ)) =
      ∏ᶠ p : Nat.Primes, primeFiberIndex W p a := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
