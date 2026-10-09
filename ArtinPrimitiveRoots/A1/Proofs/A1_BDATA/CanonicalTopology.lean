import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.LocalIndex

set_option autoImplicit false
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.LocalField
open scoped ValuativeRel
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

/-- The canonical Qp scalar embedding is continuous for the original local-field topology. -/
theorem canonical_qpadic_algebraMap_continuous (K : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] :
    let t := (inferInstance : TopologicalSpace K)
    let ν := LocalFieldTheory.localIntegerValuation K
    let L : LocalField K := ofWithZeroValuation ν
    letI : MixedWithZeroValuationContext ν := mixedWithZeroValuationContext ν
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' ν
    @Continuous ℚ_[L.residueCharacteristic] K inferInstance t
      (algebraMap ℚ_[L.residueCharacteristic] K) := by
  let t := (inferInstance : TopologicalSpace K)
  let ν := LocalFieldTheory.localIntegerValuation K
  let L : LocalField K := ofWithZeroValuation ν
  haveI : ν.Compatible := ⟨fun x y => by
    change x ≤ᵥ y ↔
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K x) ≤
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K y)
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) x y).trans
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.le_iff_le.symm⟩
  have ht : t = (Valued.mk' ν).toTopologicalSpace := by
    exact ν.toTopologicalSpace_eq
  letI : MixedWithZeroValuationContext ν := mixedWithZeroValuationContext ν
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' ν
  change @Continuous ℚ_[L.residueCharacteristic] K inferInstance t
    (algebraMap ℚ_[L.residueCharacteristic] K)
  let f := algebraMap ℚ_[L.residueCharacteristic] K
  change @Continuous ℚ_[L.residueCharacteristic] K inferInstance t f
  exact (congrArg (fun s : TopologicalSpace K =>
    @Continuous ℚ_[L.residueCharacteristic] K inferInstance s f) ht).mpr
      (continuous_qpadicNumbersAlgebra_ofWithZeroValuation ν)

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
