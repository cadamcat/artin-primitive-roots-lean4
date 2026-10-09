import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.Gamma

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Replace the quadratic multiplicative Gauss sum by the residue square sum.
Guide: PROOFS.md:476–477. Uses: A1_GAUSS residue character/additive helpers; quadraticChar_card_sqrts; additive orthogonality. -/
theorem gamma_three_eq_square_sum (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    gamma D S A 3 v.asIdeal (p : F) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
