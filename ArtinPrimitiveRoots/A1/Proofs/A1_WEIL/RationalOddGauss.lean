import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.RationalData
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.w_g.OddGaussSign

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
  classical
  have hpPrime : p.Prime := Fact.out
  letI : NeZero p := ⟨hpPrime.ne_zero⟩
  have hpOdd : Odd p := hpPrime.odd_of_ne_two hp
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hp
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  let χ : MulChar (ZMod p) ℂ := ArtinPrimitiveRoots.Proofs.w_g.quadraticCharComplex (ZMod p)
  have hprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  have hψu : ψ.mulShift (u : ZMod p) ≠ 1 := hprim (Units.ne_zero u)
  have hψ : ψ ≠ 1 := by
    intro heq
    exact (hprim one_ne_zero) (by simpa [heq])
  have hχquad : χ.IsQuadratic := by
    change ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)).IsQuadratic
    exact (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)
  have hχinv : χ⁻¹ = χ := hχquad.inv
  calc
    (∑ x : ZMod p, ZMod.stdAddChar ((u : ZMod p) * x ^ 2)) =
        gaussSum χ (ψ.mulShift (u : ZMod p)) := by
      simpa [ψ, AddChar.mulShift_apply, χ] using
        (ArtinPrimitiveRoots.Proofs.w_g.square_sum_eq_quadratic_gaussSum
          hchar (ψ.mulShift (u : ZMod p)) hψu)
    _ = χ⁻¹ (u : ZMod p) * gaussSum χ ψ :=
      gaussSum_mulShift_eq χ ψ u
    _ = χ (u : ZMod p) * (∑ x : ZMod p, ψ (x ^ 2)) := by
      rw [hχinv, ← ArtinPrimitiveRoots.Proofs.w_g.square_sum_eq_quadratic_gaussSum
        hchar ψ hψ]
    _ = (quadraticChar (ZMod p) (u : ZMod p) : ℂ) *
        ((if p % 4 = 1 then 1 else Complex.I) * (Real.sqrt (p : ℝ) : ℂ)) := by
      rw [ArtinPrimitiveRoots.Proofs.w_g.quadratic_square_sum_gauss_eval p hpOdd]
      rfl
    _ = _ := by ring

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
