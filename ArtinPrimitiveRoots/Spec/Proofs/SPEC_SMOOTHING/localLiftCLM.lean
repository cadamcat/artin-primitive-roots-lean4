import ArtinPrimitiveRoots.Proofs.spec_smoothing_b.LocalLift

set_option autoImplicit false
open NumberField Matrix MeasureTheory
open scoped MatrixGroups

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- The unsmoothed local lift is a continuous linear map with the compact-overlap norm bound.
Uses frozen `T1_l2`, `R9_proper`, `G3_volume`
and a.e. uniqueness of the fundamental-domain translate. Supplies the local L1 inputs for
the other smoothing parts and the Banach-valued identity theorem in frozen `S3_continuation`.
This is an existence theorem; choose its returned map when a named CLM is needed. -/
theorem localLiftCLM (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (W : Set (X F)) (hW : IsCompact W) :
    ∃ T : L2Space F D →L[ℂ] Lp ℂ 2 ((volX F).restrict W),
      ‖T‖ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) ∧
        ∀ u, ∀ᵐ z ∂((volX F).restrict W), T u z = l2Lift F Γ D u z := by
  exact localLiftCLM_impl Γ D hD W hW

end ArtinPrimitiveRoots.A1.Spec
