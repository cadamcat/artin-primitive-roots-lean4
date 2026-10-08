import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_scalar_FE
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_hasMellin
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_root_number_norm


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory MeasureTheory
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Mellin transport of the scalar theta equation; no Gamma product is evaluated at a pole.
Guide: sol-thin-hk2/PROOFS.md:1477–1511. Uses hk_weighted_theta_scalar_FE,
hk_weighted_theta_hasMellin and the inverse primitive/nontrivial character facts. -/
theorem hk_mellin_FE_completed [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1)
    (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) (s : ℂ) :
    hkCompleted ψ s = hkRootNumber χ T * hkCompleted (ψ⁻¹) (1 - s) := by
  classical
  have hψinv : ψ⁻¹ ≠ 1 := by
    intro h
    apply hψ
    calc
      ψ = (ψ⁻¹)⁻¹ := (inv_inv ψ).symm
      _ = (1 : RayClassGroup m →* ℂˣ)⁻¹ := congrArg Inv.inv h
      _ = 1 := by
        ext C
        simp
  have hP := hk_weighted_theta_hasMellin ψ hψ s
  have hPinv := hk_weighted_theta_hasMellin (ψ⁻¹) hψinv (1 - s)
  let z : ℂ := s / 2
  have hpoint (t : ℝ) (ht : 0 < t) :
      hkWeightedPhi ψ t⁻¹ =
        hkRootNumber χ T • ((t : ℂ) ^ ((1 : ℂ) / 2) • hkWeightedPhi (ψ⁻¹) t) := by
    have hpow : ((Real.rpow t ((1 : ℝ) / 2) : ℝ) : ℂ) =
        (t : ℂ) ^ ((1 : ℂ) / 2) := by
      calc
        ((Real.rpow t ((1 : ℝ) / 2) : ℝ) : ℂ) =
            (t : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) :=
          Complex.ofReal_cpow ht.le ((1 : ℝ) / 2)
        _ = (t : ℂ) ^ ((1 : ℂ) / 2) := by congr 1 <;> norm_num
    calc
      hkWeightedPhi ψ t⁻¹ =
          hkRootNumber χ T * ((Real.rpow t ((1 : ℝ) / 2) : ℝ) : ℂ) *
            hkWeightedPhi (ψ⁻¹) t := by
        simpa only [one_div] using (hk_weighted_theta_scalar_FE ψ χ T ht)
      _ = hkRootNumber χ T • ((t : ℂ) ^ ((1 : ℂ) / 2) • hkWeightedPhi (ψ⁻¹) t) := by
          rw [hpow]
          simp only [smul_eq_mul]
          ring
  have hMellinFE :
      mellin (fun t : ℝ => hkWeightedPhi ψ t⁻¹) (-z) =
        hkRootNumber χ T * mellin (hkWeightedPhi (ψ⁻¹)) ((1 - s) / 2) := by
    calc
      mellin (fun t : ℝ => hkWeightedPhi ψ t⁻¹) (-z) =
          mellin (fun t : ℝ =>
            hkRootNumber χ T • ((t : ℂ) ^ ((1 : ℂ) / 2) • hkWeightedPhi (ψ⁻¹) t)) (-z) := by
        rw [mellin]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [hpoint t ht]
      _ = hkRootNumber χ T •
          mellin (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) / 2) • hkWeightedPhi (ψ⁻¹) t) (-z) := by
        rw [mellin_const_smul]
      _ = hkRootNumber χ T • mellin (hkWeightedPhi (ψ⁻¹)) (-z + (1 : ℂ) / 2) := by
        rw [mellin_cpow_smul]
      _ = hkRootNumber χ T * mellin (hkWeightedPhi (ψ⁻¹)) ((1 - s) / 2) := by
        rw [smul_eq_mul]
        congr 2
        dsimp [z]
        ring
  calc
    hkCompleted ψ s = mellin (hkWeightedPhi ψ) z := hP.2.symm
    _ = mellin (fun t : ℝ => hkWeightedPhi ψ t⁻¹) (-z) := by
      simpa only [neg_neg] using (mellin_comp_inv (hkWeightedPhi ψ) (-z)).symm
    _ = hkRootNumber χ T * mellin (hkWeightedPhi (ψ⁻¹)) ((1 - s) / 2) := hMellinFE
    _ = hkRootNumber χ T * hkCompleted (ψ⁻¹) (1 - s) := by
      rw [hPinv.2]

end ArtinPrimitiveRoots.Hecke
