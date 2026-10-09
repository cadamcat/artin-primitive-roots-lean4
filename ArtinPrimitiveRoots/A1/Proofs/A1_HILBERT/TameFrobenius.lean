/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from LocalClassFieldTheory.Kummer.PowerResidueTameFormula.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameReduction

/-! Arithmetic Frobenius root quotients specified by their residue power. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped Classical ValuativeRel
open KummerTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem valuationMap_eq_zero_of_pow_eq_map_integerUnit
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    valuationMap L (Additive.ofMul beta) = 0 := by
  have hfieldUnits :
      Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u) =
        integerUnitsToFieldUnits L
          (integerUnitsMapOfValuationExtension K L u) := by
    apply Units.ext
    rfl
  have hbaseValuationMap :
      valuationMap L
          (Additive.ofMul
            (Units.map (algebraMap K L).toMonoidHom
              (integerUnitsToFieldUnits K u))) = 0 := by
    rw [hfieldUnits, valuationMap_apply, v_integerUnitsToFieldUnits]
  have hpow := valuationMap_ofMul_pow L beta (n : ℕ)
  rw [hbetaPow, hbaseValuationMap] at hpow
  exact (mul_eq_zero.mp hpow.symm).resolve_left (by
    exact_mod_cast n.ne_zero)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem integerUnitOfValuationMapZero_pow_eq_integerUnitsMap
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    integerUnitOfValuationMapZero L beta
        (valuationMap_eq_zero_of_pow_eq_map_integerUnit
          K L n u beta hbetaPow) ^ (n : ℕ) =
      integerUnitsMapOfValuationExtension K L u := by
  apply integerUnitsToFieldUnits_injective L
  calc
    integerUnitsToFieldUnits L
        (integerUnitOfValuationMapZero L beta
          (valuationMap_eq_zero_of_pow_eq_map_integerUnit
            K L n u beta hbetaPow) ^ (n : ℕ)) =
        beta ^ (n : ℕ) := by
      rw [map_pow, integerUnitOfValuationMapZero_spec]
    _ = Units.map (algebraMap K L).toMonoidHom
        (integerUnitsToFieldUnits K u) := hbetaPow
    _ = integerUnitsToFieldUnits L
        (integerUnitsMapOfValuationExtension K L u) := by
      apply Units.ext
      rfl

theorem residue_arithmeticFrobenius_integerUnitQuotient
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (u : 𝒪[L]ˣ) :
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              u / u)) =
      (residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L u)) ^
        (Nat.card 𝓀[K] - 1) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  let phi : Gal(L / K) :=
    arithmeticFrobeniusOfUnramifiedValuation K L
  let uBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L u)
  let uFrobenius : 𝒪[L]ˣ :=
    Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L phi).toMulEquiv u
  have hFrobeniusResidue :
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L uFrobenius) =
        uBar ^ Nat.card 𝓀[K] := by
    calc
      residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L uFrobenius) =
          Units.mapEquiv
            (galoisGroupResidueFieldEquivOfIsIntegralClosure K L phi).toMulEquiv
            uBar := by
        apply Units.ext
        have hval := congrArg Units.val
          (galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits
            K L phi u).symm
        simpa only [uFrobenius, uBar, residueUnitsConcreteEquiv_apply,
          Units.coe_mapEquiv] using hval
      _ = uBar ^ Nat.card 𝓀[K] := by
        apply Units.ext
        change
          galoisGroupResidueAlgEquivOfIsIntegralClosure K L phi
              (uBar : 𝓀[L]) =
            (uBar : 𝓀[L]) ^ Nat.card 𝓀[K]
        simpa only [phi] using
          galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
            K L (uBar : 𝓀[L])
  have hcardPos : 0 < Nat.card 𝓀[K] := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨0⟩
  change
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L (uFrobenius / u)) =
      uBar ^ (Nat.card 𝓀[K] - 1)
  calc
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L (uFrobenius / u)) =
        residueUnitsConcreteEquiv L
            (integerUnitsToResidueUnits L uFrobenius) / uBar := by
      simp only [map_div, uBar]
    _ = uBar ^ Nat.card 𝓀[K] / uBar := by
      rw [hFrobeniusResidue]
    _ = uBar ^ (Nat.card 𝓀[K] - 1) := by
      have hcard :
          Nat.card 𝓀[K] = (Nat.card 𝓀[K] - 1) + 1 :=
        (Nat.sub_add_cancel hcardPos).symm
      rw [hcard, pow_succ]
      simp

theorem residue_arithmeticFrobenius_kummerRootQuotient_of_dvd
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (n : ℕ+)
    (hdvd : (n : ℕ) ∣ Nat.card 𝓀[K] - 1)
    (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow :
      beta ^ (n : ℕ) =
        Units.map (algebraMap K L).toMonoidHom
          (integerUnitsToFieldUnits K u)) :
    let betaO :=
      integerUnitOfValuationMapZero L beta
        (valuationMap_eq_zero_of_pow_eq_map_integerUnit
          K L n u beta hbetaPow)
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) =
      residueUnitsConcreteEquiv L
          (residueUnitsMapOfValuationExtension K L
            (integerUnitsToResidueUnits K u)) ^
        ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
  let betaO : 𝒪[L]ˣ :=
    integerUnitOfValuationMapZero L beta
      (valuationMap_eq_zero_of_pow_eq_map_integerUnit
        K L n u beta hbetaPow)
  let betaBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L betaO)
  let uBar : 𝓀[L]ˣ :=
    residueUnitsConcreteEquiv L
      (residueUnitsMapOfValuationExtension K L
        (integerUnitsToResidueUnits K u))
  let m := (Nat.card 𝓀[K] - 1) / (n : ℕ)
  have hcard : Nat.card 𝓀[K] - 1 = (n : ℕ) * m := by
    exact (Nat.div_mul_cancel hdvd).symm.trans (Nat.mul_comm _ _)
  have hbetaOPow :
      betaO ^ (n : ℕ) = integerUnitsMapOfValuationExtension K L u := by
    simpa only [betaO] using
      integerUnitOfValuationMapZero_pow_eq_integerUnitsMap
        K L n u beta hbetaPow
  have hbetaBarPow : betaBar ^ (n : ℕ) = uBar := by
    calc
      betaBar ^ (n : ℕ) =
          residueUnitsConcreteEquiv L
            (integerUnitsToResidueUnits L (betaO ^ (n : ℕ))) := by
        rw [map_pow, map_pow]
      _ = residueUnitsConcreteEquiv L
          (integerUnitsToResidueUnits L
            (integerUnitsMapOfValuationExtension K L u)) := by
        rw [hbetaOPow]
      _ = uBar := by
        rw [← residueUnitsMap_integerUnitsToResidueUnits K L u]
  change
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) = uBar ^ m
  calc
    residueUnitsConcreteEquiv L
        (integerUnitsToResidueUnits L
          (Units.mapEquiv
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L
                (arithmeticFrobeniusOfUnramifiedValuation K L)).toMulEquiv
              betaO / betaO)) =
        betaBar ^ (Nat.card 𝓀[K] - 1) := by
      simpa only [betaBar] using
        residue_arithmeticFrobenius_integerUnitQuotient K L betaO
    _ = betaBar ^ ((n : ℕ) * m) := by rw [hcard]
    _ = (betaBar ^ (n : ℕ)) ^ m := by rw [pow_mul]
    _ = uBar ^ m := by rw [hbetaBarPow]

theorem nthRootsSubgroupMap_eq_arithmeticFrobenius_rootQuotient
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L]
    (n : ℕ+) (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hdvd : (n : ℕ) ∣ Nat.card 𝓀[K] - 1)
    (u : 𝒪[K]ˣ) (beta : Lˣ)
    (hbetaPow : beta ^ (n : ℕ) =
      Units.map (algebraMap K L).toMonoidHom (integerUnitsToFieldUnits K u))
    (z : nthRootsSubgroup K (n : ℕ))
    (hz : (localNthRootsReduction K n z).1 =
      residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K u) ^
        ((Nat.card 𝓀[K] - 1) / (n : ℕ))) :
    (nthRootsSubgroupMap K L (n : ℕ) z).1 =
      rootQuotient (K := K) (L := L) beta
        (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  let phi : Gal(L / K) := arithmeticFrobeniusOfUnramifiedValuation K L
  have hbetaPowFixed :
      ∀ sigma : Gal(L / K), sigma • (beta ^ (n : ℕ)) = beta ^ (n : ℕ) := by
    intro sigma
    rw [hbetaPow]
    exact RadicalDatum.smul_algebraMap_unit
      (K := K) (L := L) sigma (integerUnitsToFieldUnits K u)
  let quotientRoot : nthRootsSubgroup L (n : ℕ) :=
    ⟨rootQuotient (K := K) (L := L) beta phi,
      rootQuotient_mem_nthRootsSubgroup_of_pow_fixed
        (K := K) (L := L) hbetaPowFixed phi⟩
  have hnL : ValuativeRel.valuation L ((n : ℕ) : L) = 1 := by
    have hmap := (Valuation.HasExtension.val_map_eq_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) ((n : ℕ) : K)).2 hn
    simpa only [map_natCast] using hmap
  let betaO : 𝒪[L]ˣ := integerUnitOfValuationMapZero L beta
    (valuationMap_eq_zero_of_pow_eq_map_integerUnit K L n u beta hbetaPow)
  let betaFrobeniusO : 𝒪[L]ˣ := Units.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L phi).toMulEquiv betaO
  let quotientO : 𝒪[L]ˣ := betaFrobeniusO / betaO
  have hbetaOField : integerUnitsToFieldUnits L betaO = beta :=
    integerUnitOfValuationMapZero_spec L beta
      (valuationMap_eq_zero_of_pow_eq_map_integerUnit K L n u beta hbetaPow)
  have hbetaFrobeniusOField : integerUnitsToFieldUnits L betaFrobeniusO =
      phi • integerUnitsToFieldUnits L betaO := by
    apply Units.ext
    rfl
  have hquotientOField : integerUnitsToFieldUnits L quotientO =
      rootQuotient (K := K) (L := L) beta phi := by
    calc
      _ = integerUnitsToFieldUnits L betaFrobeniusO /
          integerUnitsToFieldUnits L betaO :=
        map_div (integerUnitsToFieldUnits L) betaFrobeniusO betaO
      _ = phi • integerUnitsToFieldUnits L betaO /
          integerUnitsToFieldUnits L betaO := by rw [hbetaFrobeniusOField]
      _ = phi • beta / beta := by rw [hbetaOField]
      _ = _ := rfl
  have hquotientIntegerUnit : nthRootIntegerUnit L n quotientRoot = quotientO := by
    apply integerUnitsToFieldUnits_injective L
    rw [integerUnitsToFieldUnits_nthRootIntegerUnit]
    exact hquotientOField.symm
  have hquotientResidue : residueUnitsConcreteEquiv L
      (integerUnitsToResidueUnits L quotientO) =
      residueUnitsMapOfValuationExtension K L
        (residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K u)) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
    change residueUnitsConcreteEquiv L (integerUnitsToResidueUnits L quotientO) =
      residueUnitsConcreteEquiv L
        (residueUnitsMapOfValuationExtension K L (integerUnitsToResidueUnits K u)) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ))
    exact residue_arithmeticFrobenius_kummerRootQuotient_of_dvd
      K L n hdvd u beta hbetaPow
  have hrootReduction : localNthRootsReduction L n (nthRootsSubgroupMap K L (n : ℕ) z) =
      localNthRootsReduction L n quotientRoot := by
    rw [localNthRootsReduction_nthRootsSubgroupMap]
    apply Subtype.ext
    change residueUnitsMapOfValuationExtension K L (localNthRootsReduction K n z).1 =
      integerUnitsToResidueUnits L (nthRootIntegerUnit L n quotientRoot)
    rw [hquotientIntegerUnit, hz, map_pow]
    simpa only [residueUnitsConcreteEquiv_apply] using hquotientResidue.symm
  exact congrArg Subtype.val (localNthRootsReduction_injective L n hnL hrootReduction)

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
