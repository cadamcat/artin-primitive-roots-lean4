import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Kernel support over a slightly enlarged compact coordinate set lies in one compact set in X.
The closure of the coordinate neighborhood stays in the positive chart.
Guide: `sol-thin-spec/PROOFS.md:402`. Uses frozen `G1_h3_basics`, `G2_x_action`,
`G6_ppi` and its coordinate bounds; supplies `radialKernel_compact_control`. -/
theorem radialKernel_support_thickening (k₀ : ℝ → ℝ)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ (U : Set (Coord F)) (W : Set (X F)),
      IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ posSet F ∧
        IsCompact W ∧ ∀ p ∈ closure U, ∀ w : X F, w ∉ W →
          radialKernel F k₀ (ptX F p) w = 0 := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
