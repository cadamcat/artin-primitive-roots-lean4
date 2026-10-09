import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.NativeLocalIndex

set_option autoImplicit false
open NumberField IsDedekindDomain
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.LocalField
open scoped ValuativeRel
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

attribute [local instance] nativeCompletionValuativeRel nativeCompletionLocalField

local instance (v : FinPlace F) : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

set_option backward.isDefEq.respectTransparency.types false in
/-- Normalizing the native completion valuation preserves its residue characteristic. -/
theorem nativeResidueCharacteristic_eq_ringChar (v : FinPlace F) :
    nativeResidueCharacteristic v = ringChar (𝓞 F ⧸ v.asIdeal) := by
  let C := v.adicCompletion F
  let ν := LocalFieldTheory.localIntegerValuation C
  let L := ofWithZeroValuation ν
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt C
  let w : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  letI : w.Compatible := Valuation.Compatible.ofValuation w
  have hnorm (x : C) : ν x < 1 ↔ w x < 1 := by
    change e (ValuativeRel.valuation C x) < 1 ↔ w x < 1
    have he : e (ValuativeRel.valuation C x) < 1 ↔ ValuativeRel.valuation C x < 1 := by
      simpa only [map_one] using
        (e.strictMono.lt_iff_lt (a := ValuativeRel.valuation C x) (b := 1))
    exact he.trans ((ValuativeRel.valuation C).vlt_one_iff.symm.trans w.vlt_one_iff)
  have hdiv (n : ℕ) : nativeResidueCharacteristic v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
    have hchar : ν (n : C) < 1 ↔ nativeResidueCharacteristic v ∣ n := by
      have h := L.valuationSubring_natCast_lt_one_iff_residueCharacteristic_dvd n
      change ν ((n : ν.valuationSubring) : C) < 1 ↔ nativeResidueCharacteristic v ∣ n at h
      simpa only [SubringClass.coe_natCast] using h
    rw [← hchar, hnorm]
    have hval : w (n : C) = v.valuation F (n : F) := by
      have hc : ((n : F) : C) = (n : C) := by
        change algebraMap F C (n : F) = (n : C)
        exact map_natCast (algebraMap F C) n
      simpa only [hc] using
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (n : F)
    rw [hval]
    simpa only [map_natCast] using v.valuation_lt_one_iff_mem (K := F) (n : 𝓞 F)
  letI : CharP (𝓞 F ⧸ v.asIdeal) (nativeResidueCharacteristic v) :=
    ⟨fun n => by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact (hdiv n).symm⟩
  exact (ringChar.eq (𝓞 F ⧸ v.asIdeal) (nativeResidueCharacteristic v)).symm

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
