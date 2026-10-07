import ArtinPrimitiveRoots.Spec.GeometryExtra
import ArtinPrimitiveRoots.Spec.Reduction

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The transition from the seed cusp `σ` to the evaluation cusp `σ'`, using the
representative chosen in the frozen definition of `eisTerm`. -/
def siegelTransition (Γ : Subgroup SL(2,𝓞 F)) (σ σ' : SL(2,F))
    (q : CuspCosets F Γ σ) : SL(2,F) :=
  σ⁻¹ * toSLF F ((q.out : Γ) : SL(2,𝓞 F)) * σ'

/-- Cosets contributing to the remainder at the evaluation cusp. -/
abbrev NontriangularCosets (Γ : Subgroup SL(2,𝓞 F)) (σ σ' : SL(2,F)) :=
  {q : CuspCosets F Γ σ // siegelTransition Γ σ σ' q ∉ borelSL F}

/-- The full scalar denominator lattice, including its zero element. -/
abbrev DenominatorScalars (D : ℕ) := {a : F // HasDenominatorBound F D a}

/-- Scalar association by an algebraic-integer unit. -/
def scalarUnitAssociated (a b : F) : Prop :=
  ∃ ε : (𝓞 F)ˣ, a = algebraMap (𝓞 F) F (ε : 𝓞 F) * b

/-- The nonnegative real row kernel. Heights in the consumer lemmas are positive;
all powers are explicitly real powers. -/
def siegelRowKernel (v : F × F) (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ) (α : ℝ) : ℝ :=
  ∏ w : InfinitePlace F, Real.rpow
    (y w / (Complex.normSq (w.embedding v.1 * x w + w.embedding v.2) +
      Complex.normSq (w.embedding v.1) * y w ^ 2)) α

/-- The nonnegative shifted scalar-lattice kernel in the main analytic helper. -/
def shiftedProductKernel (u : InfinitePlace F → ℂ) (l : InfinitePlace F → ℝ)
    (α : ℝ) (a : F) : ℝ :=
  ∏ w : InfinitePlace F,
    Real.rpow (Complex.normSq (w.embedding a + u w) + l w ^ 2) (-α)

end ArtinPrimitiveRoots.A1.Spec
