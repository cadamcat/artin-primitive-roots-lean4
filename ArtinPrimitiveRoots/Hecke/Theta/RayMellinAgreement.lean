import ArtinPrimitiveRoots.Hecke.Theta.RayPartialZetaReal

/-!
Mellin agreement of the ray-class functional-equation pair with its partial zeta series.
The real-integral conversion follows AINTLIB's `CompletedZeta/MellinAgreement.lean`
`heckeFEPair_Λ_real` (Chris Birkbeck, Apache-2.0).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory MeasureTheory
open NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units NumberField.Units.dirichletUnitTheorem DedekindResidue
open scoped NumberField nonZeroDivisors Real ENNReal NNReal Classical

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]

theorem rayFEPair_Λ_real [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hcop : IsCoprimeTo m (J : Ideal (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (rayFEPair m (J : Ideal (𝓞 K)) hcop).Λ (σ : ℂ) =
      (((heckeBeta K) ^ (-σ) *
        (((heckeJacobian K : ℝ≥0) : ℝ) * ∏ w : InfinitePlace K,
          Real.pi ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)) *
        ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
          rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
          (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ) := by
  let P := rayFEPair m (J : Ideal (𝓞 K)) hcop
  have hσ' : P.k < (σ : ℂ).re := hσ
  have hM := P.hasMellin hσ'
  rw [← hM.2]
  have hf : ∀ t : ℝ, P.f t - P.f₀ =
      ((rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m : ℝ) : ℂ) := by
    intro t
    change (rayF m (J : Ideal (𝓞 K)) hcop t : ℂ) - (rayPrimalConstant m : ℂ) = _
    push_cast
    rfl
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      (t : ℂ) ^ ((σ : ℂ) - 1) • (P.f t - P.f₀) =
      ((t ^ (σ - 1) * (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m) : ℝ) : ℂ) := by
    intro t ht
    rw [hf, smul_eq_mul,
      show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal]
  congr 1
  have hri : IntegrableOn (fun t : ℝ => t ^ (σ - 1) *
      (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m)) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun hM.1.re (fun t ht => ?_) measurableSet_Ioi
    rw [hpt t ht]
    exact Complex.ofReal_re _
  have hnnae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => t ^ (σ - 1) * (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m)) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht =>
      mul_nonneg (Real.rpow_nonneg ht.le _) (rayF_dev_nonneg m (J : Ideal (𝓞 K)) hcop ht)))
  have hσ0 : 0 < σ := lt_trans (by norm_num) hσ
  have h2σ : 1 < 2 * σ := by linarith
  have hβ := heckeBeta_pos K
  have hΓnn := prod_pi_rpow_mul_Gamma_nonneg K hσ0
  have hJnn : 0 ≤ ((heckeJacobian K : ℝ≥0) : ℝ) := (heckeJacobian K).2
  have hsumNN : 0 ≤ ∑' b : {b : (Ideal (𝓞 K))⁰ //
      ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
        rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
      (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-(2 * σ)) :=
    tsum_nonneg (fun b => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hENN : ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) *
      (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m)) =
      ENNReal.ofReal ((heckeBeta K) ^ (-σ) *
        (((heckeJacobian K : ℝ≥0) : ℝ) * ∏ w : InfinitePlace K,
          Real.pi ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ)) *
        ∑' b : {b : (Ideal (𝓞 K))⁰ // ∃ hb : IsCoprimeTo m (b : Ideal (𝓞 K)),
          rayClass m (b : Ideal (𝓞 K)) hb = (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹},
          (Ideal.absNorm (b.1 : Ideal (𝓞 K)) : ℝ) ^ (-(2 * σ))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hri hnnae]
    have hsplit : ∀ t ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (σ - 1) *
        (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m)) =
        ENNReal.ofReal (t ^ (σ - 1)) *
          ENNReal.ofReal (rayF m (J : Ideal (𝓞 K)) hcop t - rayPrimalConstant m) :=
      fun t ht => ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)
    rw [setLIntegral_congr_fun measurableSet_Ioi hsplit,
      lintegral_mellin_rayF_dev m J hcop hσ0,
      tsum_rayClass_ofReal_norm_sq_rpow _ h2σ,
      show ((heckeJacobian K : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((heckeJacobian K : ℝ≥0) : ℝ) from
          (ENNReal.ofReal_coe_nnreal).symm]
    rw [← ENNReal.ofReal_mul hJnn, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnnae)
    (by positivity)).mp hENN

theorem rayMellinFactor_ofReal (s : ℝ) :
    rayMellinFactor K (s : ℂ) =
      (((heckeBeta K) ^ (-(s / 2)) *
        (((heckeJacobian K : ℝ≥0) : ℝ) * ∏ w : InfinitePlace K,
          Real.pi ^ (-((mult w : ℝ) * (s / 2))) * Real.Gamma ((mult w : ℝ) * (s / 2))) : ℝ) : ℂ) := by
  classical
  unfold rayMellinFactor
  rw [show -(s : ℂ) / 2 = ((-(s / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (heckeBeta_pos K).le]
  have hprod : (∏ w : InfinitePlace K,
      (Real.pi : ℂ) ^ (-((mult w : ℂ) * (s : ℂ) / 2)) *
        Complex.Gamma ((mult w : ℂ) * (s : ℂ) / 2)) =
      ((∏ w : InfinitePlace K, Real.pi ^ (-((mult w : ℝ) * (s / 2))) *
        Real.Gamma ((mult w : ℝ) * (s / 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro w _
    have harg : (mult w : ℂ) * (s : ℂ) / 2 = (((mult w : ℝ) * (s / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_neg, ← Complex.ofReal_cpow Real.pi_pos.le,
      Complex.Gamma_ofReal, ← Complex.ofReal_mul]
  rw [hprod]
  push_cast
  ring

/-- The per-class real Mellin agreement needed for H1. -/
theorem rayFEPair_Λ_eq_partialZeta_real [IsTotallyComplex K]
    (m : RayClassModulus K) (J : (Ideal (𝓞 K))⁰)
    (hcop : IsCoprimeTo m (J : Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    (rayFEPair m (J : Ideal (𝓞 K)) hcop).Λ ((s : ℂ) / 2) =
      rayMellinFactor K (s : ℂ) *
        rayClassPartialZeta (rayClass m (J : Ideal (𝓞 K)) hcop)⁻¹ (s : ℂ) := by
  have hσ : (1 : ℝ) / 2 < s / 2 := by linarith
  rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; rfl,
    rayFEPair_Λ_real m J hcop hσ, rayMellinFactor_ofReal,
    rayClassPartialZeta_real _ hs, tsum_rayClassNormWeight_eq]
  have h2 : 2 * (s / 2) = s := by ring
  rw [h2]
  push_cast
  rfl

end ArtinPrimitiveRoots.Hecke

end
