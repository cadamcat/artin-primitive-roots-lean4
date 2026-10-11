import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_entire_L_preliminary_growth


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue
open scoped NumberField NNReal
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- Shared primitive ray-character producer for HK-H3 and A2-FE-GLUE. Its completion is
entire, its root number is unimodular, and the Gamma product is asserted only off poles.
Uses residue/trace producers, hk_root_number_norm, hk_mellin_FE_completed,
hk_completed_gamma_product and hk_entire_L_agreement. A2 supplies the idelic dictionary;
HK-H3 supplies polynomial growth from the preliminary exponential strip bounds. -/
theorem hk_fe_export_to_ext_hecke_continuation [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hp : HKPrimitive ψ) :
    Differentiable ℂ (hkEntireL ψ) ∧ Differentiable ℂ (hkEntireL (ψ⁻¹)) ∧
    (∀ s : ℂ, 1 < s.re → hkEntireL ψ s = LSeriesRay ψ s) ∧
    (∀ s : ℂ, 1 < s.re → hkEntireL (ψ⁻¹) s = LSeriesRay (ψ⁻¹) s) ∧
    Differentiable ℂ (hkCompleted ψ) ∧ Differentiable ℂ (hkCompleted (ψ⁻¹)) ∧
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      hkCompleted ψ s = hkCompletedValue (hkEntireL ψ) m s) ∧
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -(n : ℂ)) →
      hkCompleted (ψ⁻¹) s = hkCompletedValue (hkEntireL (ψ⁻¹)) m s) ∧
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      hkCompleted ψ s = W * hkCompleted (ψ⁻¹) (1 - s) := by
  classical
  have hpInv : HKPrimitive (ψ⁻¹) := by
    simpa [HKPrimitive] using
      (ArtinPrimitiveRoots.Dictionary.HKDICTRay.primitive_inv ψ hp)
  have hψInv : ψ⁻¹ ≠ 1 := by
    intro h
    apply hψ
    calc
      ψ = (ψ⁻¹)⁻¹ := (inv_inv ψ).symm
      _ = (1 : RayClassGroup m →* ℂˣ)⁻¹ := congrArg Inv.inv h
      _ = 1 := by ext C; simp
  obtain ⟨χ⟩ := hk_primitive_residue_character ψ hp
  obtain ⟨T⟩ := hk_primitive_trace_datum m
  have hL := hk_entire_L_agreement ψ hψ
  have hLInv := hk_entire_L_agreement (ψ⁻¹) hψInv
  have hcompletedDiff (η : RayClassGroup m →* ℂˣ) (hη : η ≠ 1) :
      Differentiable ℂ (hkCompleted η) := by
    have hR := rayCharacter_completed_entire (hkRayRepresentatives m) η hη
    have hq : (modulusNorm m : ℂ) ≠ 0 := by
      exact_mod_cast (ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m).ne'
    have hpow : Differentiable ℂ
        (fun s : ℂ => (modulusNorm m : ℂ) ^ (s / 2)) := by
      intro s
      exact (differentiableAt_id.div_const 2).const_cpow (Or.inl hq)
    change Differentiable ℂ (fun s : ℂ =>
      ((2 : ℂ) ^ nrComplexPlaces K /
        ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))) *
        (modulusNorm m : ℂ) ^ (s / 2) *
          (rayCharacterFEPair (hkRayRepresentatives m) η).Λ (s / 2))
    have hPdiff : Differentiable ℂ
        (fun s : ℂ => (rayCharacterFEPair (hkRayRepresentatives m) η).Λ (s / 2)) := by
      exact hR.comp (differentiable_id.div_const 2)
    have hD : Differentiable ℂ (fun s : ℂ =>
        ((2 : ℂ) ^ nrComplexPlaces K /
          ((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))) *
        ((modulusNorm m : ℂ) ^ (s / 2) *
          (rayCharacterFEPair (hkRayRepresentatives m) η).Λ (s / 2))) := by
      apply Differentiable.mul
      · exact differentiable_const _
      · apply Differentiable.mul
        · exact hpow
        · exact hPdiff
    simpa only [mul_assoc] using hD
  have hroot : ‖hkRootNumber χ T‖ = 1 := hk_root_number_norm χ T
  refine ⟨hL.1, hLInv.1, hL.2, hLInv.2,
    hcompletedDiff ψ hψ, hcompletedDiff (ψ⁻¹) hψInv, ?_, ?_,
    ⟨hkRootNumber χ T, hroot, ?_⟩⟩
  · intro s hs
    exact hk_completed_gamma_product ψ hs
  · intro s hs
    exact hk_completed_gamma_product (ψ⁻¹) hs
  · intro s
    exact hk_mellin_FE_completed ψ hψ χ T s

end ArtinPrimitiveRoots.Hecke
