import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_residue_character
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_datum


set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The residue cardinal is the norm, so the generic finite-ring Gauss norm is exactly sqrt q.
Guide: sol-thin-hk2/PROOFS.md:1307–1320. Uses hk_primitive_residue_character,
hk_primitive_trace_datum and OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm. -/
theorem hk_primitive_trace_gauss_sum [IsTotallyComplex K] {m : RayClassModulus K}
    {ψ : RayClassGroup m →* ℂˣ} (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) :
    ‖hkGaussSum χ T‖ = Real.sqrt (modulusNorm m : ℝ) ∧ hkGaussSum χ T ≠ 0 := by
  sorry

end ArtinPrimitiveRoots.Hecke
