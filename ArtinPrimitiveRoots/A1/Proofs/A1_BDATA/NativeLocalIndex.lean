import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.LocalIndex
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact

set_option autoImplicit false
open NumberField IsDedekindDomain
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.LocalField
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- The valuative relation of the literal native finite completion. -/
@[reducible]
def nativeCompletionValuativeRel (v : FinPlace F) : ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))

/-- Native valuation topology and local compactness supply the local-field structure. -/
@[instance_reducible]
def nativeCompletionLocalField (v : FinPlace F) :
    @IsNonarchimedeanLocalField (v.adicCompletion F) inferInstance
      (nativeCompletionValuativeRel v) inferInstance := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  letI : ν.IsNontrivial := inferInstance
  letI : ValuativeRel C := nativeCompletionValuativeRel v
  letI : ν.Compatible := Valuation.Compatible.ofValuation ν
  letI : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial ν).2 inferInstance
  letI : IsValuativeTopology C :=
    LocalFieldTheory.isValuativeTopology_of_valued_ofValuation C (WithZero (Multiplicative ℤ))
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

attribute [local instance] nativeCompletionValuativeRel nativeCompletionLocalField

local instance (v : FinPlace F) : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

/-- Residue characteristic of the canonical normalized local valuation. -/
def nativeResidueCharacteristic (v : FinPlace F) : ℕ :=
  (ofWithZeroValuation (LocalFieldTheory.localIntegerValuation (v.adicCompletion F))).residueCharacteristic

/-- Degree for the canonical mixed-context Qp scalar embedding. -/
def nativeCompletionDegree (v : FinPlace F) : ℕ :=
  let K := v.adicCompletion F
  let ν := LocalFieldTheory.localIntegerValuation K
  let L : LocalField K := ofWithZeroValuation ν
  letI : MixedWithZeroValuationContext ν := mixedWithZeroValuationContext ν
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' ν
  Module.finrank ℚ_[L.residueCharacteristic] K

/-- Sixth-power classes in the literal finite completion, with explicit local parameters. -/
theorem native_local_sixth_index (D : FieldData F) (v : FinPlace F) :
    Nat.card ((v.adicCompletion F)ˣ ⧸
      (powMonoidHom 6 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) =
      36 * nativeResidueCharacteristic v ^
        (nativeCompletionDegree v * padicValNat (nativeResidueCharacteristic v) 6) := by
  have hroot : IsPrimitiveRoot (D.ζ12 ^ 2) 6 := by
    simpa using D.hζ12.pow_of_dvd (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 ∣ 12)
  have hmu : ∃ ζ : v.adicCompletion F, IsPrimitiveRoot ζ 6 :=
    ⟨algebraMap F (v.adicCompletion F) (D.ζ12 ^ 2),
      hroot.map_of_injective (algebraMap F (v.adicCompletion F)).injective⟩
  exact local_sixth_index (v.adicCompletion F) hmu

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
