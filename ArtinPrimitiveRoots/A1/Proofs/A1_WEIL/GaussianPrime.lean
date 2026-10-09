import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianPrimeIntegral
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.QuadraticPrimeSum

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Assemble the exact prime comparison, for every exterior generator.
Guide: PROOFS.md:476–477. Uses: exterior_prime_index_square_sum; gamma_three_eq_square_sum. -/
theorem exterior_prime_index_gamma (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    ((W.index v (toLoc v (p⁻¹)) : ℂˣ) : ℂ) = gamma D S A 3 v.asIdeal (p : F) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
