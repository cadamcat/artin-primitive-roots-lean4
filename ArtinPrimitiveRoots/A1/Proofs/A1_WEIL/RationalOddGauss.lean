import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The actual odd-prime quadratic Gauss phase, including its sign.
Guide: PROOFS.md:482–485. Uses: Mathlib quadratic Gauss square/frobenius; standard finite additive character. -/
theorem rational_odd_gauss_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (u : (ZMod p)ˣ) :
    (∑ x : ZMod p, ZMod.stdAddChar ((u : ZMod p) * x ^ 2)) =
      (quadraticChar (ZMod p) (u : ZMod p) : ℂ) *
        (if p % 4 = 1 then 1 else Complex.I) * (Real.sqrt (p : ℝ) : ℂ) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
