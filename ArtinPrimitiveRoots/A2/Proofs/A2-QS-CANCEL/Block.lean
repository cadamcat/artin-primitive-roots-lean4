import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2b
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S2

/-!
# A2-QS-CANCEL, part C4: the residual block bound (assembly)

Guide: `runs/lanes/sol-thin-found/PROOFS.md:528-550` (`optimized_high_core` for general `κ`).
Columns in `(n, 2n]` with `n ≥ 1` exclude `⊤`, so every coprime pair has `c d ≠ ⊤` and S2
applies; sum S2 over pairs (`qsPairSum` is linear in the kernel), replace the main difference by
the boundary kernel (C1), bound it by C2b, `qs_norm_symm_M0` and `HasExponent α`
(`√(M/κ) (2n + κ^α) ≪ n√(M/κ) + √M κ^{α-1/2}`), and the remainders by C3a-C3d with one common
`η ≤ min(η₀'s, θ)`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C4 (IMPL): residual block bound
`‖Σ₃‖ ≪ (N𝔮)^8 (Mn)^δ (M + n + √M κ^{α-1/2} + n√(M/κ)) ‖z‖²`. -/
theorem qs_residual_block_bound_C4 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α)
    (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
        qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
