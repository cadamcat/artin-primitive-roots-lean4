import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The two actual dyadic finite sums needed for the valuation-parity formula.
Guide: PROOFS.md:482–485. Uses: ZMod.stdAddChar_coe; finite enumeration modulo 4 and 8. -/
theorem rational_dyadic_gauss_sums (u : ℕ) (hu : Odd u) :
    (∑ x : ZMod 4, ZMod.stdAddChar ((u : ZMod 4) * x ^ 2)) = 2 * (1 + Complex.I ^ u) ∧
    (∑ x : ZMod 8, ZMod.stdAddChar ((u : ZMod 8) * x ^ 2)) =
      4 * Complex.exp (Real.pi * Complex.I * (u : ℂ) / 4) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
