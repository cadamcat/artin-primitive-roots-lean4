import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C1

/-!
# A2-QS-CANCEL, part C2b: the paired main-term (boundary) bound

Guide: `runs/lanes/sol-thin-found/PROOFS.md:473-498` (`paired_main_bound`), lead's form: after
C1 only the boundary `κ/N t < N h ≤ κ` remains; `1/√N h ≤ √(N t/κ)` and the factor
`ψ(t)/√N t` give `1/√κ`.  `ψ(h) = χ_c(h) χ_d(h)` (`qs_gcd_pair_identity_S0` with `g = ⊤`), the
`e, t ∣ 𝔮` factors and `φ(c d)/N(c d) = (φ(c)/N c)(φ(d)/N d)` are column twists of modulus
`≤ 1` (at primes of `qsBadRad` use the local components, which are multiplicative in `c, d`);
apply `qs_divisor_pair_cauchy_C2` with `D₁ = D₂ = 1`-type trivial divisors (Dirac `μ`) and rows
`h` of norm `≤ κ`.  Divisor counts of `𝔮` cost `τ(𝔮)² ≤ (N 𝔮)²`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C2b (IMPL over C2): the boundary pair sum is
`≪ (N𝔮)² (nκ)^η √(M/κ) B1(κ, 2n) ‖z‖²`. -/
theorem qs_paired_main_bound_C2b [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M κ n : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
      (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ κ → 1 ≤ n → QSBlockCols m qS 𝔮 n cols →
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
        C * qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) * qsNorm F κ (2 * n) *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
