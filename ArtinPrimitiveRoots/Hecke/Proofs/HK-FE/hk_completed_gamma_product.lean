import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs
import DedekindResidue.CompletedZeta.MellinAgreement


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue MeasureTheory
open scoped NumberField NNReal
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Normalize H1's completed Mellin transform to the exact Deligne GammaC product, restricting
the product to regular Gamma arguments.
Uses heckeBeta, rayMellinNormalization and reciprocal Gamma cancellation. -/
theorem hk_completed_gamma_product [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    hkCompleted ψ s = hkCompletedValue (hkEntireL ψ) m s := by
  classical
  let D : ℝ := ((discr K).natAbs : ℝ)
  let q : ℝ := (modulusNorm m : ℝ)
  let J : ℂ := ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))
  have hD : 0 < D := by
    dsimp [D]
    exact DedekindResidue.natAbs_discr_pos K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have hplaces : Fintype.card (InfinitePlace K) = nrComplexPlaces K := by
    let e : InfinitePlace K ≃
        {w : InfinitePlace K // NumberField.InfinitePlace.IsComplex w} :=
      { toFun := fun w => ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
        invFun := fun w => w.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa [nrComplexPlaces] using Fintype.card_congr e
  have hprod :
      (∏ w : InfinitePlace K,
        (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
          (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹) =
        ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) ^ nrComplexPlaces K := by
    simp_rw [NumberField.IsTotallyComplex.mult_eq]
    rw [Finset.prod_const, Finset.card_univ, hplaces]
    congr 1
    congr 1 <;> ring
  have hβ : (DedekindResidue.heckeBeta K : ℂ) =
      ((4 ^ nrComplexPlaces K / D : ℝ) : ℂ) := by
    simp [heckeBeta, D]
  have hpow4_complex : ((4 : ℂ) ^ nrComplexPlaces K) ^ (s / 2) =
      (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
    calc
      ((4 : ℂ) ^ nrComplexPlaces K) ^ (s / 2) =
          (4 : ℂ) ^ ((nrComplexPlaces K : ℂ) * (s / 2)) :=
        (Complex.natCast_cpow_natCast_mul 4 (nrComplexPlaces K) (s / 2)).symm
      _ = ((2 : ℂ) ^ 2) ^ ((nrComplexPlaces K : ℂ) * (s / 2)) := by
        rw [show (4 : ℂ) = (2 : ℂ) ^ 2 by norm_num]
      _ = (2 : ℂ) ^ (2 * ((nrComplexPlaces K : ℂ) * (s / 2))) :=
        (Complex.natCast_cpow_natCast_mul 2 2
          ((nrComplexPlaces K : ℂ) * (s / 2))).symm
      _ = (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
        congr 1
        push_cast
        ring
  have hpow4 : ((4 ^ nrComplexPlaces K : ℝ) : ℂ) ^ (s / 2) =
      (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
    rw [show ((4 ^ nrComplexPlaces K : ℝ) : ℂ) =
        (4 : ℂ) ^ nrComplexPlaces K by norm_cast]
    exact hpow4_complex
  have hbase :
      ((D * q : ℝ) : ℂ) ^ (s / 2) * (heckeBeta K : ℂ) ^ (s / 2) =
        (q : ℂ) ^ (s / 2) * (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) := by
    rw [hβ, ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    have hbaseval : D * q * (4 ^ nrComplexPlaces K / D) = q * 4 ^ nrComplexPlaces K := by
      field_simp [hD.ne']
    rw [show ((D * q : ℝ) : ℂ) *
        ((4 ^ nrComplexPlaces K / D : ℝ) : ℂ) =
          ((q * 4 ^ nrComplexPlaces K : ℝ) : ℂ) by
        rw [← Complex.ofReal_mul]
        exact congrArg Complex.ofReal hbaseval]
    rw [Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (a := q) (b := 4 ^ nrComplexPlaces K)
        (by positivity) (by positivity), hpow4]
  have hGamma :
      Complex.Gammaℂ s ^ nrComplexPlaces K *
        ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) ^ nrComplexPlaces K =
        ((2 : ℂ) * (2 : ℂ) ^ (-s)) ^ nrComplexPlaces K := by
    rw [← mul_pow, Complex.Gammaℂ_def]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsplit : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) =
        (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
      exact Complex.mul_cpow_ofReal_nonneg (a := 2) (b := Real.pi)
        (by norm_num) Real.pi_pos.le (-s)
    have hpicancel : (Real.pi : ℂ) ^ (-s) * (Real.pi : ℂ) ^ s = 1 := by
      rw [← Complex.cpow_add _ _ hpi]
      simp
    have hΓs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    congr 1
    calc
      2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
          ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) =
        2 * (2 : ℂ) ^ (-s) *
          ((Real.pi : ℂ) ^ (-s) * (Real.pi : ℂ) ^ s) *
          (Complex.Gamma s * (Complex.Gamma s)⁻¹) := by
            rw [hsplit]
            ring
      _ = 2 * (2 : ℂ) ^ (-s) := by rw [hpicancel, mul_inv_cancel₀ hΓs]; ring
  have hscale :
      ((D * q : ℝ) : ℂ) ^ (s / 2) * Complex.Gammaℂ s ^ nrComplexPlaces K *
        (J⁻¹ * (heckeBeta K : ℂ) ^ (s / 2) *
          ∏ w : InfinitePlace K,
            (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
              (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹) =
        (2 : ℂ) ^ nrComplexPlaces K / J * (q : ℂ) ^ (s / 2) := by
    rw [hprod]
    calc
      _ = (((D * q : ℝ) : ℂ) ^ (s / 2) * (heckeBeta K : ℂ) ^ (s / 2) *
            (Complex.Gammaℂ s ^ nrComplexPlaces K *
              ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) ^ nrComplexPlaces K)) * J⁻¹ := by
        ring
      _ = ((q : ℂ) ^ (s / 2) * (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) *
            ((2 : ℂ) * (2 : ℂ) ^ (-s)) ^ nrComplexPlaces K) * J⁻¹ := by
        rw [hbase, hGamma]
      _ = (2 : ℂ) ^ nrComplexPlaces K / J * (q : ℂ) ^ (s / 2) := by
        rw [mul_pow]
        have hcancel :
            (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) *
              ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K = 1 := by
          calc
            _ = (2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s + (-s) * nrComplexPlaces K) := by
              rw [← Complex.cpow_mul_nat, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
            _ = 1 := by
              rw [show ((nrComplexPlaces K : ℂ) * s + (-s) * nrComplexPlaces K) = 0 by ring,
                Complex.cpow_zero]
        calc
          _ = ((q : ℂ) ^ (s / 2) * (2 : ℂ) ^ nrComplexPlaces K) *
              ((2 : ℂ) ^ ((nrComplexPlaces K : ℂ) * s) *
                ((2 : ℂ) ^ (-s)) ^ nrComplexPlaces K) * J⁻¹ := by ring
          _ = (2 : ℂ) ^ nrComplexPlaces K / J * (q : ℂ) ^ (s / 2) := by
            rw [hcancel]
            ring
  unfold hkCompleted hkCompletedValue hkEntireL rayMellinNormalization
  change (2 : ℂ) ^ nrComplexPlaces K / J * (q : ℂ) ^ (s / 2) *
      (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2) =
    ((D * q : ℝ) : ℂ) ^ (s / 2) * Complex.Gammaℂ s ^ nrComplexPlaces K *
      ((J⁻¹ * (heckeBeta K : ℂ) ^ (s / 2) *
        ∏ w : InfinitePlace K,
          (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
            (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹) *
        (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2))
  calc
    _ = (((D * q : ℝ) : ℂ) ^ (s / 2) * Complex.Gammaℂ s ^ nrComplexPlaces K *
          (J⁻¹ * (heckeBeta K : ℂ) ^ (s / 2) *
            ∏ w : InfinitePlace K,
              (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹)) *
          (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2) := by
      exact congrArg (fun z : ℂ => z *
        (rayCharacterFEPair (hkRayRepresentatives m) ψ).Λ (s / 2)) hscale.symm
    _ = _ := by ring

end ArtinPrimitiveRoots.Hecke
