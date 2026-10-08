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
  have hmul (A B : NumberFieldFractionalIdealGroup K) :
      idealNormR K (A * B) = idealNormR K A * idealNormR K B := by
    simp [DedekindResidue.idealNormR, Units.val_mul,
      FractionalIdeal.absNorm.map_mul, Rat.cast_mul]
  have hinv (A : NumberFieldFractionalIdealGroup K) :
      idealNormR K (A⁻¹) = (idealNormR K A)⁻¹ := by
    have hRat :
        FractionalIdeal.absNorm ((A⁻¹ : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (𝓞 K)⁰ K) =
          (FractionalIdeal.absNorm (A : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc
        FractionalIdeal.absNorm ((A⁻¹ : NumberFieldFractionalIdealGroup K) :
            FractionalIdeal (𝓞 K)⁰ K) *
            FractionalIdeal.absNorm (A : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.absNorm
              ((A⁻¹ * A : NumberFieldFractionalIdealGroup K) :
                FractionalIdeal (𝓞 K)⁰ K) := by
              rw [← FractionalIdeal.absNorm.map_mul, ← Units.val_mul]
        _ = 1 := by rw [inv_mul_cancel, Units.val_one, FractionalIdeal.absNorm_one]
    rw [DedekindResidue.idealNormR, DedekindResidue.idealNormR, hRat, Rat.cast_inv]
  have hmod : idealNormR K (hkModulusUnit m) = (modulusNorm m : ℝ) := by
    rw [DedekindResidue.idealNormR]
    simp [hkModulusUnit, idealUnit, FractionalIdeal.coeIdeal_absNorm]
    rw [modulusIdeal_absNorm]
  have hdiff : idealNormR K (hkDifferentUnit K) = ((discr K).natAbs : ℝ) := by
    rw [DedekindResidue.idealNormR]
    simp [hkDifferentUnit, idealUnit, FractionalIdeal.coeIdeal_absNorm]
    rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
  calc
    idealNormR K (hkDualIdeal m I) =
        (idealNormR K (hkModulusUnit m * hkDifferentUnit K * I))⁻¹ := by
      rw [hkDualIdeal, hinv]
    _ = (idealNormR K (hkModulusUnit m) *
        idealNormR K (hkDifferentUnit K) * idealNormR K I)⁻¹ := by
      rw [hmul, hmul]
    _ = ((modulusNorm m : ℝ) * ((discr K).natAbs : ℝ) *
        idealNormR K I)⁻¹ := by rw [hmod, hdiff]

end ArtinPrimitiveRoots.Hecke
