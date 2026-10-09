/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Root-choice and splitting lemmas adapted from GlobalHilbertSymbol.Core.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
import Mathlib.FieldTheory.KummerExtension

/-! Transport of the actual radical symbol through a valued field equivalence. -/

set_option autoImplicit false

open KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

theorem simpleKummerSplits
    (K E : Type) [Field K] [Field E] [Algebra K E]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : K) (β : E)
    (hβ : β ^ (n : ℕ) = algebraMap K E b)
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    Polynomial.IsSplittingField K E
      (Polynomial.X ^ (n : ℕ) - Polynomial.C b) := by
  have hβint : IsIntegral K β := IsIntegral.of_pow n.pos (by
    rw [hβ]
    exact isIntegral_algebraMap)
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    obtain ⟨ζ, hζ⟩ := hmu
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (((mem_primitiveRoots n.pos).mp hζ).map_of_injective
        (algebraMap K E).injective) hβ
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hgen,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        hβint.isAlgebraic]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff,
      Polynomial.mem_rootSet_of_ne (Polynomial.X_pow_sub_C_ne_zero n.pos b),
      Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, hβ, sub_self]

private theorem simpleKummerSemilinearEquiv
    (K K' : Type) [Field K] [Field K'] (eK : K ≃+* K')
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnK' : ((n : ℕ) : K') ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmu' : (primitiveRoots (n : ℕ) K').Nonempty) (b : Kˣ) :
    ∃ eL : chosenSimpleKummerExtension K n hnK b ≃+*
        chosenSimpleKummerExtension K' n hnK' (Units.map eK.toMonoidHom b),
      ∀ x : K, eL (algebraMap K (chosenSimpleKummerExtension K n hnK b) x) =
        algebraMap K'
          (chosenSimpleKummerExtension K' n hnK' (Units.map eK.toMonoidHom b)) (eK x) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let b' := Units.map eK.toMonoidHom b
  let E' := chosenSimpleKummerExtension K' n hnK' b'
  let β : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let β' : E'ˣ := chosenSimpleKummerRootUnit K' n hnK' b'
  letI : Algebra K K' := eK.toRingHom.toAlgebra
  letI : Algebra K E' := ((algebraMap K' E').comp eK.toRingHom).toAlgebra
  letI : IsScalarTower K K' E' := IsScalarTower.of_algebraMap_eq' rfl
  have halg (x : K) : algebraMap K E' x = algebraMap K' E' (eK x) := rfl
  have hgen : IntermediateField.adjoin K {(β' : E')} = ⊤ := by
    let R := IntermediateField.adjoin K {(β' : E')}
    apply top_unique
    intro z hzTop
    clear hzTop
    have hz : z ∈ IntermediateField.adjoin K' {(β' : E')} := by
      rw [chosenSimpleKummerExtension_adjoin_root_eq_top K' n hnK' b']
      exact IntermediateField.mem_top
    change z ∈ R
    induction hz using IntermediateField.adjoin_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K _ hz
    | algebraMap c =>
        have hc := R.algebraMap_mem (eK.symm c)
        rw [halg, eK.apply_symm_apply] at hc
        exact hc
    | add x y hx hy ihx ihy => exact R.add_mem ihx ihy
    | inv x hx ihx => exact R.inv_mem ihx
    | mul x y hx hy ihx ihy => exact R.mul_mem ihx ihy
  have hβ' : (β' : E') ^ (n : ℕ) = algebraMap K E' (b : K) := by
    exact congrArg Units.val (chosenSimpleKummerRootUnit_pow K' n hnK' b')
  let p := Polynomial.X ^ (n : ℕ) - Polynomial.C (b : K)
  letI : Polynomial.IsSplittingField K E p := simpleKummerSplits K E n hmu (b : K)
    (β : E) (congrArg Units.val (chosenSimpleKummerRootUnit_pow K n hnK b))
    (chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK b)
  letI : Polynomial.IsSplittingField K E' p :=
    simpleKummerSplits K E' n hmu (b : K) (β' : E') hβ' hgen
  let eL : E ≃ₐ[K] E' :=
    (Polynomial.IsSplittingField.algEquiv E p).trans
      (Polynomial.IsSplittingField.algEquiv E' p).symm
  exact ⟨eL.toRingEquiv, fun x => eL.commutes x⟩

theorem simpleSymbolRootQuotient
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    Units.map (algebraMap K (chosenSimpleKummerExtension K n hnK b)).toMonoidHom
        ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) =
      rootQuotient (K := K) (L := chosenSimpleKummerExtension K n hnK b)
        (chosenSimpleKummerRootUnit K n hnK b) (simpleArtin K n hnK hmu b a) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let σ := simpleArtin K n hnK hmu b a
  let e := nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu
  have hmap : Units.map (algebraMap K E).toMonoidHom
      ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) =
      (chosenSimpleKummerRootCharacter K n hnK hmu b σ).1 := congrArg Subtype.val
    (e.apply_symm_apply (chosenSimpleKummerRootCharacter K n hnK hmu b σ))
  exact hmap.trans
    (congrArg Subtype.val (chosenSimpleKummerRootCharacter_apply K n hnK hmu b σ))

theorem rootQuotientSamePow
    (K E : Type) [Field K] [Field E] [Algebra K E]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (b : Kˣ) (β γ : Eˣ)
    (hβ : β ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b)
    (hγ : γ ^ (n : ℕ) = Units.map (algebraMap K E).toMonoidHom b)
    (σ : Gal(E/K)) :
    rootQuotient (K := K) (L := E) β σ =
      rootQuotient (K := K) (L := E) γ σ := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := E) n
  let δ : D.carrier := ⟨b, β, hβ⟩
  let hfixed := nthRootsOfUnity_fixed (K := K) (L := E) n
    (nthRootsOfUnityInBase_of_primitiveRoots (K := K) (L := E) n hmu)
  exact (D.rootCharacter_eq_of_same_pow hfixed δ hβ σ).trans
    (D.rootCharacter_eq_of_same_pow hfixed δ hγ σ).symm

theorem simpleSymbolHom_semilinear
    (K K' : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
    (eK : K ≃+* K') (hExt : SemilinearValuationCompatible K K' eK)
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hnK' : ((n : ℕ) : K') ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hmu' : (primitiveRoots (n : ℕ) K').Nonempty) (a b : Kˣ) :
    Units.map eK.toMonoidHom
        ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) =
      ((simpleSymbolHom K' n hnK' hmu' (Units.map eK.toMonoidHom b)
        (Units.map eK.toMonoidHom a) : rootsOfUnity (n : ℕ) K') : K'ˣ) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let a' := Units.map eK.toMonoidHom a
  let b' := Units.map eK.toMonoidHom b
  let E' := chosenSimpleKummerExtension K' n hnK' b'
  letI : FiniteDimensional K E := chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E := chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : FiniteDimensional K' E' :=
    chosenSimpleKummerExtension_finiteDimensional K' n hnK' b'
  letI : IsAbelianGalois K' E' :=
    chosenSimpleKummerExtension_isAbelianGalois K' n hnK' hmu' b'
  obtain ⟨eL, hcomm⟩ := simpleKummerSemilinearEquiv K K' eK n hnK hnK' hmu hmu' b
  let β : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let β' : E'ˣ := chosenSimpleKummerRootUnit K' n hnK' b'
  let γ : E'ˣ := Units.map eL.toMonoidHom β
  let σ := simpleArtin K n hnK hmu b a
  let τ := simpleArtin K' n hnK' hmu' b' a'
  have hγ : γ ^ (n : ℕ) = Units.map (algebraMap K' E').toMonoidHom b' := by
    rw [show γ = Units.map eL.toMonoidHom β from rfl, ← map_pow,
      chosenSimpleKummerRootUnit_pow K n hnK b]
    apply Units.ext
    exact hcomm (b : K)
  have haction : eL (σ (β : E)) = τ (eL (β : E)) :=
    abelianLocalArtinMonoidHom_semilinear_action K K' E E'
      eK eL hcomm hExt a (β : E)
  have hquot : Units.map eL.toMonoidHom (rootQuotient (K := K) (L := E) β σ) =
      rootQuotient (K := K') (L := E') γ τ := by
    apply Units.ext
    simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map,
      AlgEquiv.smul_units_def]
    change eL (σ (β : E) / (β : E)) = τ (eL (β : E)) / eL (β : E)
    rw [map_div₀, haction]
  apply Units.map_injective (f := (algebraMap K' E').toMonoidHom)
    (algebraMap K' E').injective
  calc
    _ = Units.map eL.toMonoidHom
        (Units.map (algebraMap K E).toMonoidHom
          ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ)) := by
      apply Units.ext
      exact (hcomm _).symm
    _ = Units.map eL.toMonoidHom (rootQuotient (K := K) (L := E) β σ) :=
      congrArg (Units.map eL.toMonoidHom) (simpleSymbolRootQuotient K n hnK hmu a b)
    _ = rootQuotient (K := K') (L := E') γ τ := hquot
    _ = rootQuotient (K := K') (L := E') β' τ :=
      rootQuotientSamePow K' E' n hmu' b' γ β' hγ
        (chosenSimpleKummerRootUnit_pow K' n hnK' b') τ
    _ = _ := (simpleSymbolRootQuotient K' n hnK' hmu' a' b').symm

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
