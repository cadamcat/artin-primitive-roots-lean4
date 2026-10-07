import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2

/-!
# A2-QS-CANCEL, part C3: the remainder terms of the error tuple

Guide: `runs/lanes/sol-thin-found/PROOFS.md:499-550` (table of prefactors and divisor-product
conditions; estimate (E); the per-term substitutions).  Common method: split rows `a₀` into
dyads `(B, 2B]`, `B ≤ κ`, the divisors `e ∣ 𝔮 f` into `e_𝔮 e₁ e₂` with `e₁ ∣ c`, `e₂ ∣ d` in
dyads `(D₁,2D₁]`, `(D₂,2D₂]`; apply `qs_divisor_pair_cauchy_C2`; bound
`B1(2B, 2n/D_i) = B1(2n/D_i, 2B)` (`qs_norm_symm_M0`) by `HasExponent α`; sum the dyads
(`α - 1/2 > 0`).  The divisor cutoff ratio is `Λ = (M n)^η`.  Weights that depend on
`N(cd)^{-1/2}` are absorbed into `z(c)/√N c` (columns in `(n, 2n]`).

Original pieces (`E₄` highDiv, `E₀` res, `E₅` trans): no dependence on `N(cd)` except through
the divisor; Dirac `μ`.  Dual pieces (`E₁` highDiv, `E₂` res): `M/(N e √N(cd)) · Z` does not
depend on `N(cd)`; `E₂` carries `N(cd)^{-1/2}`.  Dual transition `E₃`: the weight depends on
`N(cd)` through `Z = √(N e N(cd)/(M N a₀))` inside `T(TW∘sq)`; smooth dyadic cutoff in `N(cd)`
and inverse Mellin with a majorant from `qs_transform_bounds_P0` (found:466-470).
Tails: rapid decay (`qs_transform_bounds_P0`, `qs_tail_bound_M1`) with a large exponent `A`
chosen after the polynomial losses; the dual high-core tail needs the margin
`N𝔮 n² (M n)^θ ≤ κ M` (in the optimized range `κ M = N² P^η'`, `n = N/N g`).
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C3a (IMPL): original remainders `E₄` (high divisors), `E₀` (zero residue), `E₅`
(transition) are `≪ (N𝔮)^8 (Mn)^δ (M + n + √M κ^{α-1/2} + n√(M/κ)) ‖z‖²`. -/
theorem qs_orig_remainders_C3a [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsOrigKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) 𝔮)‖ +
            ‖qsPairSum cols z (qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) 𝔮)‖ +
            ‖qsPairSum cols z (qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

/-- C3b (IMPL): dual main-type remainders `E₁` (high divisors) and `E₂` (the transformed
residue at zero, retained for every field). -/
theorem qs_dual_main_remainders_C3b [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮)‖ +
            ‖qsPairSum cols z (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

/-- C3c (SOL-LEAD): the dual transition remainder `E₃`, whose weight depends on the product of
the column norms; inverse Mellin separation with an integrable majorant. -/
theorem qs_dual_transition_C3c [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        ‖qsPairSum cols z (qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

/-- C3d (IMPL): rapid tails (both inner tails and the dual high-core kernel), under the margin
`N𝔮 n² (Mn)^θ ≤ κ M`. -/
theorem qs_tails_C3d [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (θ : ℝ) (hθ : 0 < θ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsPairSum cols z (fun c d =>
            qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
              qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
              qsDualHighKernel F W M κ 𝔮 c d)‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ (-1 : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
