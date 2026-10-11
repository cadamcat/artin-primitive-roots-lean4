import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_point_ideal_integral
import ArtinPrimitiveRoots.Proofs.hkfe_poisson_p.WeightedRescale


set_option autoImplicit false
open NumberField ClassFieldTheory IsDedekindDomain DedekindResidue
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Principal rescaling preserves the normalized weighted unit-box average.
Uses hk_point_ideal_integral, weighted Gaussian
reindexing, product formula and the full-unit box retile, as in heckeG_principal_mul. -/
theorem hk_weighted_normalized_class_invariance [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (I J : NumberFieldFractionalIdealGroup K)
    (h : ClassGroup.mk K I = ClassGroup.mk K J) {t : ℝ} (ht : 0 < t) :
    hkNormalizedG ψ I t = hkNormalizedG ψ J t := by
  obtain ⟨y, hIJ⟩ := (DedekindResidue.classGroup_mk_eq_mk_iff K).mp h
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K y
  have hnorm : idealNormR K (P * I) =
      ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) * idealNormR K I := by
    simpa [P] using DedekindResidue.idealNormR_principal_mul K I y
  have hIpos := idealNormR_pos K I
  have hypos : 0 < ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) := by
    rw [Rat.cast_pos, abs_pos]
    exact Algebra.norm_ne_zero_iff.mpr (Units.ne_zero y)
  have harg : (idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t =
      ((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 *
    ((idealNormR K (P * I))⁻¹ ^ 2 * heckeBeta K * t) := by
    rw [hnorm]
    field_simp [hypos.ne', hIpos.ne']
  rw [← hIJ]
  unfold hkNormalizedG
  have hNJpos := idealNormR_pos K (P * I)
  have hβ := heckeBeta_pos K
  have hradial : 0 ≤ (idealNormR K (P * I))⁻¹ ^ 2 * heckeBeta K * t := by
    positivity
  change hkWeightedG ψ I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t) =
    hkWeightedG ψ (P * I) ((idealNormR K (P * I))⁻¹ ^ 2 * heckeBeta K * t)
  calc
    hkWeightedG ψ I ((idealNormR K I)⁻¹ ^ 2 * heckeBeta K * t) =
        hkWeightedG ψ I (((|Algebra.norm ℚ (y : K)| : ℚ) : ℝ) ^ 2 *
          ((idealNormR K (P * I))⁻¹ ^ 2 * heckeBeta K * t)) := by rw [harg]
    _ = hkWeightedG ψ (P * I) ((idealNormR K (P * I))⁻¹ ^ 2 * heckeBeta K * t) :=
      (hkWeightedG_principal_mul ψ I y hradial).symm

end ArtinPrimitiveRoots.Hecke
