import ArtinPrimitiveRoots.A1.Field
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness

set_option autoImplicit false
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.LocalField
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

/-- The sixth-power quotient count with finiteness supplied by local-field structure. -/
theorem local_sixth_index (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ 6) :
    let v := LocalFieldTheory.localIntegerValuation K
    let F : LocalField K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v := mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Nat.card (Kˣ ⧸ (powMonoidHom 6 : Kˣ →* Kˣ).range) =
      36 * F.residueCharacteristic ^
        (Module.finrank ℚ_[F.residueCharacteristic] K * padicValNat F.residueCharacteristic 6) := by
  classical
  let v := LocalFieldTheory.localIntegerValuation K
  let F : LocalField K := ofWithZeroValuation v
  letI : MixedWithZeroValuationContext v := mixedWithZeroValuationContext v
  letI valuedK : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  letI : Finite (Kˣ ⧸ (powMonoidHom 6 : Kˣ →* Kˣ).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_natCast_ne_zero K 6 (by norm_num)
  obtain ⟨a, e⟩ := chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation v
    (LocalFieldTheory.localIntegerValuation_surjective K)
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let A := ZMod (F.residueCharacteristic ^ a) × (Fin d → ℤ_[F.residueCharacteristic])
  letI : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  letI : Finite (A ⧸ LocalFieldTheory.nsmulAddSubgroup A 6) := by infer_instance
  let emul : U ≃* Multiplicative A := by
    letI : TopologicalSpace K := valuedK.toTopologicalSpace
    exact e.symm.toMulEquiv
  letI : Finite (U ⧸ (powMonoidHom 6 : U →* U).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv U (Multiplicative A) 6 emul
  have hker : Nat.card ((powMonoidHom 6 : Kˣ →* Kˣ).ker) = 6 := by
    rw [← rootsOfUnity_eq_ker]
    obtain ⟨ζ, hζ⟩ := hmu
    exact hζ.card_rootsOfUnity
  change Nat.card (Kˣ ⧸ (powMonoidHom 6 : Kˣ →* Kˣ).range) =
    36 * F.residueCharacteristic ^ (d * padicValNat F.residueCharacteristic 6)
  have hindex := mixed_fieldIndex v (LocalFieldTheory.localIntegerValuation_surjective K) (n := 6)
  simpa only [hker, ← Nat.mul_assoc, Nat.reduceMul] using hindex

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
