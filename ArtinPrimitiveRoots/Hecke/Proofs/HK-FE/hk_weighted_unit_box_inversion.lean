import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_gaussian_poisson


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Integrate the weighted Poisson equation over the full unit box and retile the dual log
variables. Guide: sol-thin-hk2/PROOFS.md:1409–1439. Uses hk_weighted_gaussian_poisson,
the Gaussian majorants of H1 and HeckeTheta's dualShift / fundamental-domain integral. -/
theorem hk_weighted_unit_box_inversion [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (I : NumberFieldFractionalIdealGroup K) {u : ℝ} (hu : 0 < u) :
    hkWeightedG ψ I u =
      (charValue ψ T.B * hkGaussSum χ T /
        ((modulusNorm m : ℂ) *
          ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
            Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) * (Real.sqrt u : ℂ))) *
        hkWeightedG (ψ⁻¹) (hkDualIdeal m I)
          ((4 : ℝ) ^ (2 * nrComplexPlaces K) / u) := by
  sorry

end ArtinPrimitiveRoots.Hecke
