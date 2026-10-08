import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.smoothing_uniform_eval_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.smoothing_smooth_representative

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Transport the bounded continuous value map to L2 of the compact image in X, retaining its
representative. Guide: `sol-thin-spec/PROOFS.md:409`. Uses `smoothing_uniform_eval_bound`
at order zero, `smoothing_smooth_representative`, and frozen `G1_h3_basics`, `G3_volume`.
Supplies the compact Lp conjunct of frozen `S1_smoothing`. -/
theorem smoothing_toLp (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ T : L2Space F D →L[ℂ] Lp ℂ 2 ((volX F).restrict (ptX F '' K)),
      ∀ u, ∀ᵐ z ∂(volX F), z ∈ ptX F '' K →
        T u z = smoothingOperator F k₀ (l2Lift F Γ D u) z := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
