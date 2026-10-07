import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# A2-QS-CANCEL, part C2: divisor-pair Cauchy–Schwarz with separated smooth arguments

Guide: `runs/lanes/sol-thin-found/PROOFS.md:459-472` (the common pair tool).

Shape.  For coprime column pairs `(c, d)` (columns of norm `≤ 2n`), divisors `e₁ ∣ c`, `e₂ ∣ d`
in norm dyads `(D₁, 2D₁]`, `(D₂, 2D₂]`, rows `a` (squarefree admissible, norm `≤ 2B`) and a
row twist `|ρ| ≤ 1`, the weight `Φ(N a, N(e₁e₂), N(cd))` may depend on the product of the
column norms only through a mixture `∫ x^{it} φ(y,u,t) dμ(t)` over a finite measure `μ`
(`μ` a Dirac mass covers weights independent of `x`; `μ = ` Lebesgue with a density covers the
inverse Mellin separation of found:466-470).  Proof: Fubini over `t`; `N(cd)^{it}` is a diagonal
twist of modulus one; remove `(c,d) = 1` by Möbius over `k ∣ (c,d)`; reindex `c = lcm(k,e₁) c'`
using `qs_family_mul_S0`; Cauchy–Schwarz in the rows; `qs_energy_le_norm_M0`; monotonicity;
divisor multiplicities by `qs_divisor_bound_M1` and `qs_ideal_count_M1`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

open Classical in
/-- C2 (OPUS): divisor-pair Cauchy–Schwarz with separated smooth arguments. -/
theorem qs_divisor_pair_cauchy_C2 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n B D₁ D₂ Λ : ℝ) (cols rows : Finset (Ideal (𝓞 K))) (z ρ : Ideal (𝓞 K) → ℂ)
        (μ : Measure ℝ) [IsFiniteMeasure μ] (φ : ℝ → ℝ → ℝ → ℂ) (Φ : ℝ → ℝ → ℝ → ℂ)
        (gmaj : ℝ → ℝ),
        1 ≤ n → 1 ≤ B → 1 ≤ D₁ → 1 ≤ D₂ →
        (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * n) →
        (∀ a ∈ rows, QSAdm m qS a ∧ qsN a ≤ 2 * B) →
        (∀ a, ‖ρ a‖ ≤ 1) →
        (∀ y u x : ℝ, Φ y u x = ∫ t, ((x : ℂ) ^ ((t : ℂ) * Complex.I)) * φ y u t ∂μ) →
        Integrable gmaj μ → (∀ y u t, ‖φ y u t‖ ≤ gmaj t) → ∫ t, gmaj t ∂μ ≤ Λ →
        ‖qsPairSum cols z (fun c d =>
            ∑ e₁ ∈ (qsDivisors c).filter (fun e => D₁ < qsN e ∧ qsN e ≤ 2 * D₁),
              ∑ e₂ ∈ (qsDivisors d).filter (fun e => D₂ < qsN e ∧ qsN e ≤ 2 * D₂),
                (qsMu (e₁ * e₂) : ℂ) *
                  ∑ a ∈ rows, ρ a * (F.character c).idealValue a *
                    (F.character d).idealValue a * Φ (qsN a) (qsN (e₁ * e₂)) (qsN (c * d)))‖ ≤
          C * (n * B) ^ η * Λ * Real.sqrt (D₁ * D₂) *
            Real.sqrt (qsNorm F (2 * B) (2 * n / D₁) * qsNorm F (2 * B) (2 * n / D₂)) *
              ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
