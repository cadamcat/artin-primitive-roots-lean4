import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Compute the stabilized uniformizer Gaussian as the exact exterior residue square sum.
Guide: PROOFS.md:476–477. Uses: A.integral; A.trivial_on_F; A.unramified; W.stable; residue-ball cosets. -/
theorem exterior_prime_index_square_sum (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (W : LocalGaussianData A) (v : FinPlace F) (hv : v ∉ S.Sf)
    (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    ((W.index v (toLoc v (p⁻¹)) : ℂˣ) : ℂ) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
