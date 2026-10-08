import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_weighted_theta_eq_ray_character
import DedekindResidue.CompletedZeta.MellinAgreement


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue MeasureTheory
open ArtinPrimitiveRoots.Hecke.Theta
open scoped NumberField NNReal
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The conductor-scaled theta's Mellin transform, valid for every complex argument.
Guide: sol-thin-hk2/PROOFS.md:1477–1537. Uses hk_weighted_theta_eq_ray_character,
H1's zero-constant strong FE pair and the positive scaling t/q of the Mellin integral. -/
theorem hk_weighted_theta_hasMellin [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (s : ℂ) :
    HasMellin (hkWeightedPhi ψ) (s / 2) (hkCompleted ψ s) := by
  classical
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  letI : Fintype (RayClassGroup m) := Fintype.ofFinite _
  let R := hkRayRepresentatives m
  let P := rayCharacterFEPair R ψ
  let q : ℝ := (modulusNorm m : ℝ)
  let J : ℂ := ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))
  let A : ℂ := (2 : ℂ) ^ nrComplexPlaces K / J
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have hP : IsStrongFEPair P := by
    constructor
    · exact finiteFEPair_f₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => rayFEPair m (R.ideal C) (R.coprime C))
        (rayPrimalConstant m : ℂ) (fun _ => rfl) (1 / 2) (by norm_num)
        (fun _ => rfl)
    · exact finiteFEPair_g₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => rayFEPair m (R.ideal C) (R.coprime C))
        (rayDualConstant m : ℂ) (fun _ => by simp [rayFEPair]) (1 / 2) (by norm_num)
        (fun _ => rfl)
  have hPM : HasMellin P.f (s / 2) (P.Λ (s / 2)) := hP.hasMellin (s / 2)
  have hpoint (t : ℝ) (ht : 0 < t) :
      hkWeightedPhi ψ t = A • P.f (t / q) := by
    unfold hkWeightedPhi
    change A * hkWeightedH ψ (t / q) = A • P.f (t / q)
    rw [hk_weighted_theta_eq_ray_character ψ hψ (div_pos ht hq)]
    simpa only [smul_eq_mul, P, R]
  have hchange : (fun t : ℝ => P.f (t / q)) = fun t => P.f (q⁻¹ * t) := by
    funext t
    congr 1
    dsimp [q]
    rw [div_eq_mul_inv, mul_comm]
  have hcomp : MellinConvergent (fun t : ℝ => P.f (t / q)) (s / 2) := by
    rw [hchange]
    exact (MellinConvergent.comp_mul_left (f := P.f) (s := s / 2)
      (a := q⁻¹) (inv_pos.mpr hq)).2 hPM.1
  have hscaled : MellinConvergent (fun t : ℝ => A • P.f (t / q)) (s / 2) :=
    hcomp.const_smul A
  have hconv : MellinConvergent (hkWeightedPhi ψ) (s / 2) := by
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • hkWeightedPhi ψ t)
      (Set.Ioi 0)
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • (A • P.f (t / q)))
      (Set.Ioi 0) at hscaled
    exact IntegrableOn.congr_fun hscaled (fun t ht => by rw [hpoint t ht])
      measurableSet_Ioi
  have hqpow : ((q⁻¹ : ℝ) : ℂ) ^ (-(s / 2)) = (q : ℂ) ^ (s / 2) := by
    rw [show ((q⁻¹ : ℝ) : ℂ) = (q : ℂ)⁻¹ by norm_cast,
      Complex.inv_cpow_ofReal_nonneg hq.le, Complex.cpow_neg, inv_inv]
  have hscaleM : mellin (fun t : ℝ => P.f (t / q)) (s / 2) =
      ((q⁻¹ : ℝ) : ℂ) ^ (-(s / 2)) • mellin P.f (s / 2) := by
    rw [hchange, mellin_comp_mul_left (f := P.f) (s := s / 2)
      (a := q⁻¹) (inv_pos.mpr hq)]
  have hval : mellin (hkWeightedPhi ψ) (s / 2) =
      A * (q : ℂ) ^ (s / 2) * P.Λ (s / 2) := by
    calc
      mellin (hkWeightedPhi ψ) (s / 2) = mellin (fun t => A • P.f (t / q)) (s / 2) := by
        rw [mellin]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
        rw [hpoint t ht]
      _ = A • mellin (fun t => P.f (t / q)) (s / 2) := by
        rw [mellin_const_smul]
      _ = A • (((q⁻¹ : ℝ) : ℂ) ^ (-(s / 2)) • mellin P.f (s / 2)) := by
        rw [hscaleM]
      _ = A * (q : ℂ) ^ (s / 2) * P.Λ (s / 2) := by
        rw [smul_eq_mul, smul_eq_mul, hqpow, hPM.2]
        ring
  change MellinConvergent (hkWeightedPhi ψ) (s / 2) ∧
    mellin (hkWeightedPhi ψ) (s / 2) = hkCompleted ψ s
  refine ⟨hconv, ?_⟩
  rw [hval]
  change A * (q : ℂ) ^ (s / 2) * P.Λ (s / 2) =
    A * (modulusNorm m : ℂ) ^ (s / 2) *
      (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2)
  rw [show (q : ℂ) = (modulusNorm m : ℂ) by norm_cast]

end ArtinPrimitiveRoots.Hecke
