import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_gaussian_poisson
import ArtinPrimitiveRoots.Proofs.hkfe_poisson_p.WeightedRescale


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory
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
  classical
  let q : ℝ := (4 : ℝ) ^ (2 * nrComplexPlaces K) / u
  let C : ℂ := charValue ψ T.B * hkGaussSum χ T /
    ((modulusNorm m : ℂ) *
      ((idealNormR K I * (1 / 2 : ℝ) ^ nrComplexPlaces K *
        Real.sqrt ((discr K).natAbs : ℝ) : ℝ) : ℂ) * (Real.sqrt u : ℂ))
  let b := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis ℝ
  have hprod (v : logSpace K) :
      ∏ w : InfinitePlace K, (heckeWeights K u v w) ^ mult w = u :=
    DedekindResidue.prod_heckeWeights_pow_mult K hu v
  have hdualWeights (v : logSpace K) :
      (fun w => 4 / heckeWeights K u v w) =
        heckeWeights K q (-v + dualShift K) := by
    funext w
    have hnotReal : ¬ IsReal w :=
      not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
    have h := congrFun (DedekindResidue.dualPlaceWeights_heckeWeights_eq K hu v) w
    simpa [q, DedekindResidue.dualPlaceWeights, hnotReal, div_eq_mul_inv] using h
  have htheta (v : logSpace K) :
      hkWeightedTheta ψ I (heckeWeights K u v) =
        C * hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I)
          (heckeWeights K q (-v + dualShift K)) := by
    have hp := hk_weighted_gaussian_poisson ψ χ T I (heckeWeights K u v)
      (fun w => heckeWeights_pos K hu v w)
    rw [hprod, hdualWeights] at hp
    simpa [C, q] using hp
  have hshift :
      ∫ v in ZSpan.fundamentalDomain b,
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I)
            (heckeWeights K q (-v + dualShift K)) =
        ∫ v in ZSpan.fundamentalDomain b,
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (heckeWeights K q v) := by
    refine setIntegral_fundamentalDomain_comp_neg_add_complex b (dualShift K)
      (fun v => hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (heckeWeights K q v)) ?_
    intro l v
    have hl : (l : logSpace K) ∈ unitLattice K :=
      (le_of_eq ((Module.Free.chooseBasis ℤ (unitLattice K)).ofZLatticeBasis_span ℝ)) l.2
    obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hl
    rw [add_comm, ← ha]
    exact hkWeightedTheta_heckeWeights_periodic (ψ⁻¹) (hkDualIdeal m I) q v
      (Additive.toMul a)
  have hInt :
      ∫ v in ZSpan.fundamentalDomain b, hkWeightedTheta ψ I (heckeWeights K u v) =
        C * ∫ v in ZSpan.fundamentalDomain b,
          hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (heckeWeights K q v) := by
    calc
      ∫ v in ZSpan.fundamentalDomain b, hkWeightedTheta ψ I (heckeWeights K u v) =
          ∫ v in ZSpan.fundamentalDomain b,
            C * hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I)
              (heckeWeights K q (-v + dualShift K)) := by
            refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b)
              (fun v _ => htheta v)
      _ = C * ∫ v in ZSpan.fundamentalDomain b,
            hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I)
              (heckeWeights K q (-v + dualShift K)) := by
            rw [MeasureTheory.integral_const_mul]
      _ = C * ∫ v in ZSpan.fundamentalDomain b,
            hkWeightedTheta (ψ⁻¹) (hkDualIdeal m I) (heckeWeights K q v) := by
            rw [hshift]
  unfold hkWeightedG
  rw [hInt]
  dsimp [C, q]
  ring

end ArtinPrimitiveRoots.Hecke
