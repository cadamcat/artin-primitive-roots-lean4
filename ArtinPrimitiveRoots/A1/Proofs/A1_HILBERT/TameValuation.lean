import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameGlobalUnit
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameReduction

/-! The normalized completion valuation and the global principal-ideal exponent. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Classical ValuativeRel
open GlobalClassFieldTheory.Reciprocity
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable {F : Type} [Field F] [NumberField F]

theorem absoluteCompletion_valuationMap_count
    (v : FinPlace F) (x : Fˣ) :
    let C := absoluteCompletion v
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    valuationMap C
      (Additive.ofMul (Units.map (algebraMap F C).toMonoidHom x)) =
      -FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) := by
  let C := absoluteCompletion v
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let piData := chosenFinitePlaceCompletionIntegralUniformizer v
  have hpiGlobalVal : v.valuation F (piData.integer : F) =
      WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact piData.intValuation_eq_exp_neg_one
  have hpiNe : (piData.integer : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff (v.valuation F)).mp
    rw [hpiGlobalVal]
    simp
  let piF : Fˣ := Units.mk0 (piData.integer : F) hpiNe
  let j : Fˣ →* Cˣ := Units.map (algebraMap F C).toMonoidHom
  let piC : Cˣ := j piF
  have hpiC : (piC : C) = (piData.completionInteger : C) :=
    piData.coe_completionInteger.symm
  have hpiIrreducible : Irreducible piData.completionInteger := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    let completionDVF : ValuationTheory.DiscreteValuationField.DVF C :=
      { ValueGroup := ValuativeRel.ValueGroupWithZero C
        valuation := ValuativeRel.valuation C }
    exact completionDVF.maximalIdeal_eq_span_uniformizer
      piData.completionInteger_isUniformizer
  have hpiLocalVal : valuationMap C (Additive.ofMul piC) = -1 := by
    rw [valuationMap_apply]
    exact v_integerRingIrreducibleFieldUnit C piData.completionInteger
      hpiIrreducible piC hpiC
  let k : ℤ := WithZero.log (v.valuation F (x : F))
  let w : Fˣ := x * piF ^ k
  have hxGlobalVal : v.valuation F (x : F) = WithZero.exp k :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr x.ne_zero)).symm
  have hwGlobalVal : v.valuation F (w : F) = 1 := by
    simp only [w, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [map_mul, map_zpow₀]
    change v.valuation F (x : F) * v.valuation F (piData.integer : F) ^ k = 1
    rw [hpiGlobalVal, ← WithZero.exp_zsmul]
    simp only [zsmul_eq_mul, mul_neg_one]
    rw [hxGlobalVal, ← WithZero.exp_add]
    simp
  have hwResidue : residue v (w : F) ≠ 0 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one
      v (w : F)).mpr hwGlobalVal
  obtain ⟨wO, hwO, _⟩ := absoluteCompletionUnit_residue v w hwResidue
  have hwLocalZero : valuationMap C (Additive.ofMul (j w)) = 0 := by
    rw [← hwO, valuationMap_apply]
    exact v_integerUnitsToFieldUnits C wO
  have hwLocal : j w = j x * piC ^ k := by
    change j (x * piF ^ k) = j x * j piF ^ k
    rw [map_mul, map_zpow]
  rw [hwLocal, valuationMap_ofMul_mul, valuationMap_ofMul_zpow,
    hpiLocalVal] at hwLocalZero
  have hxLocal : valuationMap C (Additive.ofMul (j x)) = k := by
    apply sub_eq_zero.mp
    simpa only [mul_neg_one, sub_eq_add_neg] using hwLocalZero
  change valuationMap C (Additive.ofMul (j x)) = _
  rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (x : F) x.ne_zero, neg_neg]
  exact hxLocal

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
