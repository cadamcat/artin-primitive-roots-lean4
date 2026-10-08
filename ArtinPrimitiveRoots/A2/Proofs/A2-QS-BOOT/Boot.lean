import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».Block
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M2
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0Slice

/-!
# A2-QS-BOOT: monotone row norm, finite descent, bootstrap and the core theorem

Guide: `runs/lanes/sol-thin-found/PROOFS.md:482-496` (III.6, monotone up-to row norm),
`553-582` (B0-B2).  Numeric cores already compiled in `runs/lanes/sol-thin-found/wt/
ArtinPrimitiveRoots/Review/sol-thin-found/`: `MonotoneBootstrap.monotone_threshold_improvement`
(imports `OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents`, prebuilt),
`SieveAlgebra.exponent_step`, `SieveAlgebra.optimized_scale_identity`.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- Row split (IMPL; RETIER `qs_monotone_row_norm`, found:484-487): the squarefree rows of norm
`≤ κ` give `B1(κ, N)`; the rows with `κ < N a ≤ M` have `sf(a) = N a > κ` and `W(N a/M) ≥ 1`,
so they are dominated by the high-core matrix. -/
theorem qs_row_split_B (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) (hκ : 0 ≤ κ) :
    qsNorm F M N ≤ qsNorm F κ N + qsHighNorm F W M N κ := by
  sorry

/-- B0 (SOL-LEAD; RETIER `qs_boot_parameters_B0`): the high-core norm in the optimized range,
by `r ≥ 40/ε` successive gcd descents with the original `G = N^{1/r}` (`qs_gcd_descent_S0`),
class/dyad slicing (`qs_class_dyad_slice_pos_S0`; rows are empty at `M = 0`), the residual form (`qs_residual_form_S0`), the
block bound (`qs_residual_block_bound_C4`) with `n = N/N g`, `𝔮 = qsBadRad · g`,
`Σ_{N g ≤ G} (N𝔮)^8 ≪ G^{9+η}`, and the terminal unit-column case.  Here
`κ = N²/M · (MN)^η` and `2N(MN)^η ≤ M ≤ N²`. -/
theorem qs_high_core_bound_B0 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N →
      2 * N * (M * N) ^ η ≤ M → M ≤ N ^ (2 : ℝ) →
      qsHighNorm F W M N (N ^ (2 : ℝ) / M * (M * N) ^ η) ≤
        C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  sorry

/-- Recursion (IMPL): `HasExponent α ⇒ B1(M,N) ≪_δ (MN)^δ (M + N + N^{2α-1} M^{1-α})` for
`M ≥ N ≥ 1` (found:556-570): row split at `κ = N²/M (MN)^η`, `B1(κ,N) = B1(N,κ) ≪ N + κ^α`
with `κ^α ≤ N^{2α-1}M^{1-α}(MN)^{αη}`, B0 for the high rows; endpoints `M ≥ N²` (exponent
`α ≤ 2`) and `N ≤ M < 2N(MN)^η` (`N^α = N^{2α-1}M^{1-α}(M/N)^{α-1}`); a cap weight exists by
`qs_cap_weight_exists_P0`. -/
theorem qs_upTo_recursion_B [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      qsNorm F M N ≤ C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  sorry

/-- B1 (IMPL; numeric core `monotone_threshold_improvement`): the recursion and monotonicity
(`qs_norm_mono_M0`) give `HasExponent (2 - 1/α)` (`M' = max(M, N^{2-1/α})`, found:571-576). -/
theorem qs_boot_step_B1 (F : QSFamily m qS) (α : ℝ) (hα1 : 1 ≤ α)
    (hrec : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ N → N ≤ M →
      qsNorm F M N ≤ C * (M * N) ^ δ * (M + N + N ^ (2 * α - 1) * M ^ (1 - α))) :
    QSHasExponent F (2 - 1 / α) := by
  sorry

/-- B2 (IMPL): the iteration `α₀ = 2`, `α_{j+1} = 2 - 1/α_j = 1 + 1/(j+2)` (M2, recursion,
B1; `exponent_step`). -/
theorem qs_exponent_iteration_B2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    ∀ j : ℕ, QSHasExponent F (1 + 1 / ((j : ℝ) + 1)) := by
  sorry

/-- B2 (IMPL): the sharp core bound (found:577-582): choose `j` with `1/(j+1) < ε/4`; then
`N^{α_j} ≤ N (MN)^{ε/4}`. -/
theorem qs_core_large_sieve_B2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    QSCoreBound F := by
  sorry

end ArtinPrimitiveRoots.A2
