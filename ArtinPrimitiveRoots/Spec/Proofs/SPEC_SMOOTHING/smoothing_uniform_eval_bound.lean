import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_compact_control
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.param_deriv_integral_formula
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.localLiftCLM

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Every fixed derivative evaluation on a compact coordinate set defines a bounded continuous
linear map, with its local L1/Cauchy–Schwarz bound. Constants are independent of the L2 vector.
Guide: `sol-thin-spec/PROOFS.md:406`. Uses `radialKernel_compact_control`,
`param_deriv_integral_formula`, `localLiftCLM`, and frozen `G3_volume` and `T1_l2`.
Supplies the derivative-map conjunct of frozen `S1_smoothing` and generic maps for S3. -/
theorem smoothing_uniform_eval_bound (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (k₀ : ℝ → ℝ) (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F)
    (n : ℕ) (v : Fin n → Coord F) :
    ∃ (W : Set (X F)) (C : ℝ) (T : L2Space F D →L[ℂ] (K →ᵇ ℂ)),
      IsCompact W ∧ 0 ≤ C ∧
        ‖T‖ ≤ C * Real.sqrt ((volX F).real W) *
          Real.sqrt (overlapMultiplicity F Γ W : ℝ) ∧
        ∀ u p, T u p = iteratedFDeriv ℝ n
          (fun q => smoothingOperator F k₀ (l2Lift F Γ D u) (ptX F q)) p.1 v := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
