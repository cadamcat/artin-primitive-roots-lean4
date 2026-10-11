import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_inversion
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_normalized_class_invariance


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Sum normalized ideal theta over ordinary classes, using the actual dual-class permutation.
Uses hk_weighted_normalized_inversion,
hk_weighted_normalized_class_invariance and classRep. LEAD. -/
theorem hk_weighted_class_sum_inversion [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (χ : HKResidueCharacter ψ) (T : HKTraceDatum m)
    {t : ℝ} (ht : 0 < t) :
    hkWeightedH ψ (1 / t) =
      hkRootNumber χ T * (Real.sqrt (t / (modulusNorm m : ℝ)) : ℂ) *
        hkWeightedH (ψ⁻¹) (t / (modulusNorm m : ℝ) ^ 2) := by
  classical
  have hq : 0 < (modulusNorm m : ℝ) := by
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have htq : 0 < t / (modulusNorm m : ℝ) ^ 2 := by positivity
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans
      (Equiv.mulLeft ((ClassGroup.mk K (hkModulusUnit m * hkDifferentUnit K))⁻¹))
  have he (C : ClassGroup (𝓞 K)) : e C = hkDualClass m C := rfl
  have hclass (C : ClassGroup (𝓞 K)) :
      ClassGroup.mk K (hkDualIdeal m (classRep K C)) =
        ClassGroup.mk K (classRep K (e C)) := by
    rw [mk_classRep, he]
    simp [hkDualIdeal, hkDualClass, map_mul, map_inv, mk_classRep, mul_comm]
  have hterm (C : ClassGroup (𝓞 K)) :
      hkNormalizedG (ψ⁻¹) (hkDualIdeal m (classRep K C))
        (t / (modulusNorm m : ℝ) ^ 2) =
      hkNormalizedG (ψ⁻¹) (classRep K (e C)) (t / (modulusNorm m : ℝ) ^ 2) :=
    hk_weighted_normalized_class_invariance (ψ⁻¹) _ _ (hclass C) htq
  unfold hkWeightedH
  simp_rw [hk_weighted_normalized_inversion ψ χ T _ ht, hterm]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp e (fun C =>
    hkNormalizedG (ψ⁻¹) (classRep K C) (t / (modulusNorm m : ℝ) ^ 2))

end ArtinPrimitiveRoots.Hecke
