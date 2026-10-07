import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory IsDedekindDomain DedekindResidue
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Norm of the conductor-and-different dual ideal, with all divisions in R.
Guide: sol-thin-hk2/PROOFS.md:1426–1434. Uses absNorm_differentIdeal, modulusNorm and idealNormR. -/
theorem hk_dual_ideal_norm (m : RayClassModulus K) (I : NumberFieldFractionalIdealGroup K) :
    idealNormR K (hkDualIdeal m I) =
      ((modulusNorm m : ℝ) * ((discr K).natAbs : ℝ) * idealNormR K I)⁻¹ := by
  sorry

end ArtinPrimitiveRoots.Hecke
