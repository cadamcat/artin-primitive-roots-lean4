import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_point_ideal_integral
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_residue_character
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_datum


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Finite Fourier expansion followed by the translated anisotropic Gaussian Poisson theorem.
The full theta keeps the zero point at q=1. Guide: sol-thin-hk2/PROOFS.md:1359–1408.
Uses hk_point_ideal_integral, residue principal values, trace-value/ideal_eq of T and H1 Poisson;
the complex-place dual weights are 4/c, not 1/c. -/
theorem hk_weighted_gaussian_poisson [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    (I : NumberFieldFractionalIdealGroup K) (c : InfinitePlace K → ℝ)
    (hc : ∀ w, 0 < c w) :
    hkWeightedTheta ψ I c =
      (charValue ψ T.B * hkGaussSum χ T /
        ((modulusNorm m : ℂ) *
          ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
            Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) *
          (Real.sqrt (∏ w : InfinitePlace K, c w ^ mult w) : ℂ))) *
        hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (fun w => 4 / c w) := by
  sorry

end ArtinPrimitiveRoots.Hecke
