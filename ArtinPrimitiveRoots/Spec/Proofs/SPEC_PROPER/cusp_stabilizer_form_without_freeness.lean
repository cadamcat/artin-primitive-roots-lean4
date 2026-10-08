import ArtinPrimitiveRoots.Spec.Proofs.SPEC_PROPER.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Every cusp stabilizer has a unit diagonal and a uniformly bounded denominator,
and acts by the affine horizontal map and the squared-norm height map.
Guide: sol-thin-spec/PROOFS.md:134–142 and 205. Uses G1_h3_basics and
G2_x_action, with no FreeAction assumption; feeds siegel_high_height_overlap_finite.
This exposes only the free-independent form/action components needed from R2. -/
theorem cusp_stabilizer_form_without_freeness
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    ∃ D : ℕ, 0 < D ∧ ∀ γ : cuspStab F Γ σ,
      ∃ ε : (𝓞 F)ˣ, ∃ μ : F, HasDenominatorBound F D μ ∧
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ ∧
        ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
          (∀ w, 0 < y w) →
          (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) =
            σ • ptX' F
              (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
                w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
              (fun w => Complex.normSq
                (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w) := by
  sorry
end ArtinPrimitiveRoots.A1.Spec
