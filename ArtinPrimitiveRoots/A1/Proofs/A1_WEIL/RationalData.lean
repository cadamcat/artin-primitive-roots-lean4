import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Remove the rational p-adic valuation; the resulting rational is a local unit. -/
def rationalUnitPart (p : ℕ) (a : ℚˣ) : ℚ :=
  (a : ℚ) / (p : ℚ) ^ padicValRat p (a : ℚ)

/-- Odd 2-adic unit residue, represented modulo 8. -/
def rationalDyadicResidue (a : ℚˣ) : ℕ :=
  let u := rationalUnitPart 2 a
  ((u.num : ZMod 8) * (u.den : ZMod 8)⁻¹).val

/-- The unnormalized rational finite Weil phase in the positive finite-character convention.
Uses the actual valuation, unit residue, and Jacobi symbol; not an assumed product formula. -/
def rationalPrimePhase (p : Nat.Primes) (a : ℚˣ) : ℂ :=
  let k := padicValRat p.1 (a : ℚ)
  let u := rationalUnitPart p.1 a
  if p.1 = 2 then
    if Even k then (1 + Complex.I ^ rationalDyadicResidue a) / (Real.sqrt 2 : ℂ)
    else Complex.exp (Real.pi * Complex.I * (rationalDyadicResidue a : ℂ) / 4)
  else if Even k then 1
  else (if p.1 % 4 = 1 then 1 else Complex.I) * (jacobiSym (u.num * u.den) p.1 : ℂ)

/-- The real phase for the negative archimedean additive-character convention. -/
def rationalArchPhase (a : ℚˣ) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I * (if (a : ℚ) > 0 then 1 else -1) / 4))

/-- A genuine rational diagonalization of Tr(a x²), with nonzero coefficients. -/
structure QuadraticTraceDiagonal (a : Fˣ) where
  basis : Module.Basis (Fin (Module.finrank ℚ F)) ℚ F
  coeff : Fin (Module.finrank ℚ F) → ℚˣ
  diagonal : ∀ x : F, Algebra.trace ℚ F ((a : F) * x ^ 2) =
    ∑ i, (coeff i : ℚ) * (basis.repr x i) ^ 2

def tracePrimePhase {a : Fˣ} (T : QuadraticTraceDiagonal a) (p : Nat.Primes) : ℂ :=
  ∏ i, rationalPrimePhase p (T.coeff i)

def traceArchPhase {a : Fˣ} (T : QuadraticTraceDiagonal a) : ℂ :=
  ∏ i, rationalArchPhase (T.coeff i)

/-- Finite-place fiber over a rational prime, with the actual local normalized indices. -/
def primeFiberIndex {A : AddCharData F} (W : LocalGaussianData A)
    (p : Nat.Primes) (a : Fˣ) : ℂ :=
  ∏ᶠ v : {v : FinPlace F // (p.1 : 𝓞 F) ∈ v.asIdeal},
    ((W.index v.1 (toLoc v.1 a) : ℂˣ) : ℂ)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
