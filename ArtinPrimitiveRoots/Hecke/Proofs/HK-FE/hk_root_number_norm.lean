import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_primitive_trace_gauss_sum
import ArtinPrimitiveRoots.Hecke.Theta.CFTIdealBridge

set_option autoImplicit false
open NumberField ClassFieldTheory DedekindResidue IsDedekindDomain
open scoped NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The different-normalized root number has norm one, including conductor norm one.
Guide: sol-thin-hk2/PROOFS.md:1321–1338. Uses hk_primitive_trace_gauss_sum,
finite ray-character unitarity and T.coprime. -/
theorem hk_root_number_norm [IsTotallyComplex K] {m : RayClassModulus K}
    {ψ : RayClassGroup m →* ℂˣ} (χ : HKResidueCharacter ψ) (T : HKTraceDatum m) :
    ‖hkRootNumber χ T‖ = 1 := by
  have hdenom : ‖(Real.sqrt (modulusNorm m : ℝ) : ℂ)‖ = Real.sqrt (modulusNorm m : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hG := hk_primitive_trace_gauss_sum χ T
  have hGnorm := hG.1
  have hGnz := hG.2
  have hS_pos : Real.sqrt (modulusNorm m : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero] at hGnorm
    exact hGnz (norm_eq_zero.mp hGnorm)
  have hchar : charValue ψ T.B = (ψ (rayClass m T.B T.coprime) : ℂ) := dif_pos T.coprime
  have hnorm_B : ‖charValue ψ T.B‖ = 1 := by
    rw [hchar]
    have : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
    have : Fintype (RayClassGroup m) := Fintype.ofFinite (RayClassGroup m)
    let g := rayClass m T.B T.coprime
    have hn : Fintype.card (RayClassGroup m) ≠ 0 := Fintype.card_ne_zero
    have hpow_g : g ^ Fintype.card (RayClassGroup m) = 1 := pow_card_eq_one
    have hpow_psi : (ψ g) ^ Fintype.card (RayClassGroup m) = 1 := by
      rw [← map_pow, hpow_g, map_one]
    have hpow_C : ((ψ g : ℂˣ) : ℂ) ^ Fintype.card (RayClassGroup m) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow_psi, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpow_C hn
  unfold hkRootNumber
  rw [norm_div, norm_mul, hnorm_B, one_mul, hGnorm, hdenom]
  exact div_self hS_pos

end ArtinPrimitiveRoots.Hecke
