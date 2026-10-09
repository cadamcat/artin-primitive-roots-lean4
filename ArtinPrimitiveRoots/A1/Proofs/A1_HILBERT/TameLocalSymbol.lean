/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Unramified certificate adapted from LocalClassFieldTheory.Kummer.PowerResidueTameFormula.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameFrobenius
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology

/-! The local Artin symbol of a unit radical from a supplied residue root. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped Classical ValuativeRel
open KummerTheory LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem simpleSymbolHom_unit_radical
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hdvd : (n : ℕ) ∣ Nat.card 𝓀[K] - 1)
    (u : 𝒪[K]ˣ) (z : nthRootsSubgroup K (n : ℕ))
    (hz : (localNthRootsReduction K n z).1 =
      residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K u) ^
        ((Nat.card 𝓀[K] - 1) / (n : ℕ))) (a : Kˣ) :
    simpleSymbolHom K n hnK hmu (integerUnitsToFieldUnits K u) a =
      nthRootsSubgroupEquivRootsOfUnity K (n : ℕ) z ^
        valuationMap K (Additive.ofMul a) := by
  let b : Kˣ := integerUnitsToFieldUnits K u
  let E := chosenSimpleKummerExtension K n hnK b
  let beta : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  letI : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  letI : Algebra 𝒪[K] E := Algebra.ofSubsemiring 𝒪[K]
  letI : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  letI : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  have hbetaPowUnits : beta ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom b :=
    chosenSimpleKummerRootUnit_pow K n hnK b
  have hbetaPow : (beta : E) ^ (n : ℕ) = algebraMap K E (b : K) :=
    congrArg Units.val hbetaPowUnits
  have hbVal : ValuativeRel.valuation K (b : K) = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero K
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  have hbetaVal : ValuativeRel.valuation E (beta : E) = 1 := by
    apply valuation_eq_one_of_valuationMap_eq_zero E
    exact valuationMap_eq_zero_of_pow_eq_map_integerUnit
      K E n u beta hbetaPowUnits
  have hgenIntermediate : IntermediateField.adjoin K {(beta : E)} = ⊤ :=
    chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b
  have hgen : Algebra.adjoin K {(beta : E)} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (beta : E))).mp hgenIntermediate
  letI : IsUnramifiedValuedExtension K E :=
    isUnramifiedValuedExtension_of_unit_kummer_generator
      n (b : K) (beta : E) hbVal hn hbetaVal hbetaPow hgen
  let phi : Gal(E / K) := arithmeticFrobeniusOfUnramifiedValuation K E
  let e := nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu
  let psi : Gal(E / K) →* nthRootsSubgroup K (n : ℕ) :=
    e.symm.toMonoidHom.comp (chosenSimpleKummerRootCharacter K n hnK hmu b)
  have hroot : (nthRootsSubgroupMap K E (n : ℕ) z).1 =
      rootQuotient (K := K) (L := E) beta phi :=
    nthRootsSubgroupMap_eq_arithmeticFrobenius_rootQuotient
      K E n hn hdvd u beta hbetaPowUnits z hz
  have hpsi : psi phi = z := by
    apply e.injective
    change e (e.symm (chosenSimpleKummerRootCharacter K n hnK hmu b phi)) = e z
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact (congrArg Subtype.val
      (chosenSimpleKummerRootCharacter_apply K n hnK hmu b phi)).trans hroot.symm
  have hArtin : simpleArtin K n hnK hmu b a =
      phi ^ valuationMap K (Additive.ofMul a) := by
    change abelianLocalArtinMonoidHom K E a = _
    exact abelianLocalArtinMonoidHom_eq_frobenius_zpow K E a
  change nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)
      (psi (simpleArtin K n hnK hmu b a)) = _
  rw [hArtin, map_zpow, hpsi, map_zpow]

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
