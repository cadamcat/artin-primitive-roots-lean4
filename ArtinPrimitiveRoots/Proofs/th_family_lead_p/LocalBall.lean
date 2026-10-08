import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

theorem algebraicIdealPower_mem_ball (v : FinPlace F) (n : ℕ) (x : 𝓞 F)
    (hx : x ∈ v.asIdeal ^ n) :
    (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) ∈ ball v (n : ℤ) := by
  change Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x)) ≤
    WithZero.exp (-(n : ℤ))
  have hxv : v.intValuation x ≤ WithZero.exp (-(n : ℤ)) :=
    (v.intValuation_le_pow_iff_mem x n).2 hx
  simpa [FinitePlace.embedding, HeightOneSpectrum.valuation_of_algebraMap] using hxv

end ArtinPrimitiveRoots.A1.Theta
