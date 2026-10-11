import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».RootNumber
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import ArtinPrimitiveRoots.Proofs.qs_p1_p.Analytic

/-!
# A2-QS-POISSON, part P1: primitive smooth ideal Poisson

Uses `qs_quadratic_FE_root_one` (RN),
`qs_transform_bounds_P0`, `qs_transform_mellin_P0`, `qs_tail_bound_M1`.  Proof: write
`h(N a/X)` by Mellin inversion, interchange with the absolutely convergent series on `Re s = 2`,
shift to `Re s = -σ` (`0 < σ < 1`) using strip boundedness and Phragmén–Lindelöf/Stirling for
the gamma quotient, apply `Λ(1-s) = Λ(s)`, expand `L(1-s,χ)` (absolutely convergent there) and
substitute `u = 1 - s`; the inner integral is `T h(X N b / N f)` after moving its line to
`Re u = 1/2` (holomorphy on `Re u > 0`).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- P1 (SOL-LEAD): primitive smooth ideal Poisson for a nonprincipal quadratic character of
trivial infinite type and exact conductor `f`:
`Σ'_a χ(a) h(N a/X) = X/√(N f) · Σ'_a χ(a) (T h)(X N a / N f)`; the dual series is
absolutely summable (the left one is a finite sum). -/
theorem qs_primitive_smooth_poisson_P1 [IsTotallyComplex K]
    (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f : Ideal (𝓞 K))
    (hf : IsPrimitiveConductor χ f) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1)
    (hinf : ∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1)
    (h : ℝ → ℂ) (hh : IsQSWeight h) (X : ℝ) (hX : 0 < X) :
    Summable (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖χ.idealValue a.1 *
          qsTransform K h (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ))‖) ∧
      ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, χ.idealValue a.1 * h ((Ideal.absNorm a.1 : ℝ) / X) =
        ((X / Real.sqrt (Ideal.absNorm f : ℝ) : ℝ) : ℂ) *
          ∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥}, χ.idealValue a.1 *
          qsTransform K h (X * (Ideal.absNorm a.1 : ℝ) / (Ideal.absNorm f : ℝ)) := by
  constructor
  · exact qs_p1_dual_summable χ f hf hsq hne hinf h hh X hX
  · exact qs_p1_poisson_identity χ f hf hsq hne hinf h hh X hX

end ArtinPrimitiveRoots.A2
