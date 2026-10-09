/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from LocalClassFieldTheory.Kummer.PowerResidueTameFormula.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import GaloisCohomology.Kummer.Concrete.LocalUnitKummerUnramified
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius

/-! Reduction of local roots of unity and its injectivity away from the residue characteristic. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped Classical ValuativeRel
open KummerTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem nthRootsSubgroup_valuationMap_eq_zero
    (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) :
    valuationMap K (Additive.ofMul z.1) = 0 := by
  have hpow := valuationMap_ofMul_pow K z.1 (n : ℕ)
  have hzero : ((n : ℕ) : ℤ) * valuationMap K (Additive.ofMul z.1) = 0 := by
    rw [z.2, valuationMap_ofMul_one] at hpow
    exact hpow.symm
  exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast n.ne_zero)

def nthRootIntegerUnit (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K z.1 (nthRootsSubgroup_valuationMap_eq_zero K n z)

@[simp]
theorem integerUnitsToFieldUnits_nthRootIntegerUnit
    (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) :
    integerUnitsToFieldUnits K (nthRootIntegerUnit K n z) = z.1 :=
  integerUnitOfValuationMapZero_spec K z.1 (nthRootsSubgroup_valuationMap_eq_zero K n z)

theorem nthRootIntegerUnit_pow (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) :
    nthRootIntegerUnit K n z ^ (n : ℕ) = 1 := by
  apply integerUnitsToFieldUnits_injective K
  rw [map_pow, integerUnitsToFieldUnits_nthRootIntegerUnit, z.2, map_one]

def localNthRootsReduction (n : ℕ+) :
    nthRootsSubgroup K (n : ℕ) →* rootsOfUnity (n : ℕ) 𝓀[K] where
  toFun z := ⟨integerUnitsToResidueUnits K (nthRootIntegerUnit K n z), by
    change integerUnitsToResidueUnits K (nthRootIntegerUnit K n z) ^ (n : ℕ) = 1
    rw [← map_pow, nthRootIntegerUnit_pow, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' := by
    intro z w
    apply Subtype.ext
    apply Units.ext
    rfl

@[simp]
theorem localNthRootsReduction_apply (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) :
    (localNthRootsReduction K n z).1 =
      integerUnitsToResidueUnits K (nthRootIntegerUnit K n z) := rfl

theorem localNthRootsReduction_nthRootsSubgroupMap
    (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ+) (z : nthRootsSubgroup K (n : ℕ)) :
    localNthRootsReduction L n (nthRootsSubgroupMap K L (n : ℕ) z) =
      ⟨residueUnitsMapOfValuationExtension K L (localNthRootsReduction K n z).1, by
        change residueUnitsMapOfValuationExtension K L
          (localNthRootsReduction K n z).1 ^ (n : ℕ) = 1
        rw [← map_pow, (localNthRootsReduction K n z).2, map_one]⟩ := by
  apply Subtype.ext
  change integerUnitsToResidueUnits L
      (nthRootIntegerUnit L n (nthRootsSubgroupMap K L (n : ℕ) z)) =
    residueUnitsMapOfValuationExtension K L
      (integerUnitsToResidueUnits K (nthRootIntegerUnit K n z))
  rw [residueUnitsMap_integerUnitsToResidueUnits]
  congr 1
  apply Units.ext
  apply Subtype.ext
  rfl

theorem localNthRootsReduction_injective (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1) :
    Function.Injective (localNthRootsReduction K n) := by
  intro z w hzw
  let zO : 𝒪[K]ˣ := nthRootIntegerUnit K n z
  let wO : 𝒪[K]ˣ := nthRootIntegerUnit K n w
  have hzPow : zO ^ (n : ℕ) = 1 := nthRootIntegerUnit_pow K n z
  have hwPow : wO ^ (n : ℕ) = 1 := nthRootIntegerUnit_pow K n w
  let f : Polynomial 𝒪[K] := Polynomial.X ^ (n : ℕ) - 1
  have hzRoot : f.IsRoot (zO : 𝒪[K]) := by
    rw [Polynomial.IsRoot.def]
    dsimp only [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    apply sub_eq_zero.mpr
    exact congrArg Units.val hzPow
  have hwRoot : f.IsRoot (wO : 𝒪[K]) := by
    rw [Polynomial.IsRoot.def]
    dsimp only [f]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    apply sub_eq_zero.mpr
    exact congrArg Units.val hwPow
  have hresUnits : residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K wO) =
      residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K zO) := by
    change (localNthRootsReduction K n w).1 = (localNthRootsReduction K n z).1
    exact congrArg Subtype.val hzw.symm
  have hres : IsLocalRing.residue 𝒪[K] (wO : 𝒪[K]) =
      IsLocalRing.residue 𝒪[K] (zO : 𝒪[K]) := by
    calc
      _ = ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K wO) :
          𝓀[K]ˣ) : 𝓀[K]) := (integerUnitsToResidueUnits_apply K wO).symm
      _ = ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K zO) :
          𝓀[K]ˣ) : 𝓀[K]) := congrArg Units.val hresUnits
      _ = _ := integerUnitsToResidueUnits_apply K zO
  have hnUnit : IsUnit ((n : ℕ) : 𝒪[K]) := by
    apply (Valuation.integer.integers
      (ValuativeRel.valuation K)).isUnit_iff_valuation_eq_one.mpr
    exact hn
  have hderiv : IsUnit (f.derivative.eval (zO : 𝒪[K])) := by
    simpa [f, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.eval_mul] using
      hnUnit.mul (zO.isUnit.pow ((n : ℕ) - 1))
  have hwz : (wO : 𝒪[K]) = (zO : 𝒪[K]) :=
    eq_of_simple_roots_of_residue_eq hzRoot hwRoot hres hderiv
  have hO : zO = wO := Units.ext hwz.symm
  apply Subtype.ext
  calc
    z.1 = integerUnitsToFieldUnits K zO :=
      (integerUnitsToFieldUnits_nthRootIntegerUnit K n z).symm
    _ = integerUnitsToFieldUnits K wO := congrArg _ hO
    _ = w.1 := integerUnitsToFieldUnits_nthRootIntegerUnit K n w

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
