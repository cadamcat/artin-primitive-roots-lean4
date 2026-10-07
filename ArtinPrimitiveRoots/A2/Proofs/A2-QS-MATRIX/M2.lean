import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0

/-!
# A2-QS-MATRIX, part M2: the initial exponent `HasExponent 2`

Guide: `runs/lanes/sol-thin-found/PROOFS.md:327-328`.  Smooth Gram expansion of
`Σ_a W(N a/M) |Σ_c z_c χ_c(a)|²` (rows coprime to `m`, `qS`; `W ≥ 1` on `[0,1]` dominates the
squarefree rows of norm `≤ M`), class slicing, gcd grouping (`qs_gcd_pair_identity_S0`):
diagonal pairs cost `≪ M ‖z‖²`; a nonprincipal residual pair kernel is `≪ √N f (N𝔮 N f)^η`
(`qs_pair_kernel_bound_M2`: Möbius over `e ∣ 𝔮`, P1, decay of `T W`, ideal counts), and
Cauchy–Schwarz over the `≪ N^{1+η}` columns gives `N^{2+O(η)} ‖z‖²`.  No use of the quadratic
bound being proved or of the A2 zero-free theorem.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- M2a (IMPL over P1): the smooth kernel of a nonprincipal primitive quadratic character,
`|Σ'_{(a,𝔮)=1} W(N a/M) χ(a)| ≪_η (N𝔮 · N f)^η √(N f)`, uniformly in `M ≥ 1`. -/
theorem qs_pair_kernel_bound_M2 [IsTotallyComplex K] (W : ℝ → ℝ) (hW : IsCapWeight W)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : ArtinPrimitiveRoots.A1.HeckeChar K) (f 𝔮 : Ideal (𝓞 K)) (M : ℝ),
      IsPrimitiveConductor χ f → χ ^ 2 = 1 → χ ≠ 1 →
      (∀ w : InfinitePlace K, ∀ u : w.Completionˣ, χ.locInf w u = 1) →
      Squarefree 𝔮 → IsCoprime 𝔮 f → 1 ≤ M →
      ‖qsTot (fun x => (W x : ℂ)) M 𝔮 χ‖ ≤
        C * (qsN 𝔮 * qsN f) ^ η * Real.sqrt (qsN f) := by
  sorry

/-- M2 (IMPL over M2a, S0; RETIER `qs_hasExponent_two_M2`): `B1(M,N) ≪_ε (MN)^ε (M + N²)`. -/
theorem qs_hasExponent_two_M2 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) :
    QSHasExponent F 2 := by
  sorry

end ArtinPrimitiveRoots.A2
