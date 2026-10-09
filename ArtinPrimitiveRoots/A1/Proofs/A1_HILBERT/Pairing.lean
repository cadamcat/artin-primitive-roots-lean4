/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from ClassFieldTheory's MaximalLocalKummerPairing and LocalHilbertPairing.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Core
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality

/-! Multiplicativity in the radical variable, by restriction of local Artin maps. -/

set_option autoImplicit false

open KummerTheory LocalClassFieldTheory LocalFieldTheory RamificationTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private abbrev radicalExtension (n : ℕ+) :=
  kummerRadicalExtension (K := K) (Omega := SeparableClosure K) n
    (maximalKummerSubgroup K n).1

private def radicalArtin (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Kˣ →* Gal((radicalExtension K n)/K) := by
  let Δ := maximalKummerSubgroup K n
  let M := radicalExtension K n
  letI : FiniteDimensional K M :=
    maximalKummerRadicalExtension_finiteDimensional K n hnK hmu
  letI : IsAbelianGalois K M :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := SeparableClosure K) n hmu Δ.1
  exact abelianLocalArtinMonoidHom K M

private def radicalPairingSource (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    Kˣ →* nthRootsSubgroup (radicalExtension K n) (n : ℕ) := by
  let Δ := maximalKummerSubgroup K n
  let M := radicalExtension K n
  let hΔ : Δ.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := M) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hnK Δ.1
  let incl : Kˣ →* Δ.1 :=
    { toFun := fun b => ⟨b, by simp [Δ, maximalKummerSubgroup]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let σ : Gal(M/K) := radicalArtin K n hnK hmu a
  let evaluate : (Gal(M/K) →* nthRootsSubgroup M (n : ℕ)) →*
      nthRootsSubgroup M (n : ℕ) :=
    { toFun := fun χ => χ σ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact evaluate.comp ((restrictedSubgroupKummerCharacter n hmu Δ hΔ).comp incl)

private def radicalPairing (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    Kˣ →* rootsOfUnity (n : ℕ) K :=
  (nthRootsSubgroupEquivRootsOfUnity K (n : ℕ)).toMonoidHom.comp
    ((nthRootsSubgroupEquivOfPrimitiveRoots
      K (radicalExtension K n) n hmu).symm.toMonoidHom.comp
        (radicalPairingSource K n hnK hmu a))

private theorem radicalPairing_map_rootQuotient
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ)
    (β : (radicalExtension K n)ˣ)
    (hβ : β ^ (n : ℕ) = Units.map (algebraMap K (radicalExtension K n)).toMonoidHom b) :
    Units.map (algebraMap K (radicalExtension K n)).toMonoidHom
        ((radicalPairing K n hnK hmu a b : rootsOfUnity (n : ℕ) K) : Kˣ) =
      rootQuotient (K := K) (L := radicalExtension K n) β
        (radicalArtin K n hnK hmu a) := by
  let Δ := maximalKummerSubgroup K n
  let M := radicalExtension K n
  let hΔ : Δ.1 ≤ finiteKummerRadicalSubgroup (K := K) (L := M) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension n hnK Δ.1
  let incl : Kˣ →* Δ.1 :=
    { toFun := fun c => ⟨c, by simp [Δ, maximalKummerSubgroup]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let σ : Gal(M/K) := radicalArtin K n hnK hmu a
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := M) n
  let δ : D.carrier := restrictedRadicalInclusion n Δ hΔ (incl b)
  let hfixed := restrictedKummerFixed (K := K) (L := M) n hmu
  let e := nthRootsSubgroupEquivOfPrimitiveRoots K M n hmu
  have hβ' : β ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom δ.1 := by
    change β ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom b
    exact hβ
  have hmap : Units.map (algebraMap K M).toMonoidHom
      ((radicalPairing K n hnK hmu a b : rootsOfUnity (n : ℕ) K) : Kˣ) =
      (radicalPairingSource K n hnK hmu a b).1 :=
    congrArg Subtype.val (e.apply_symm_apply (radicalPairingSource K n hnK hmu a b))
  calc
    _ = (radicalPairingSource K n hnK hmu a b).1 := hmap
    _ = rootQuotient (K := K) (L := M) β σ := by
      change D.rootCharacter δ hfixed σ = rootQuotient (K := K) (L := M) β σ
      exact (D.rootCharacter_eq_of_same_pow hfixed δ hβ' σ).symm

private theorem simpleSymbolHom_map_rootQuotient
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

private theorem rootQuotient_inclusion
    {Ω : Type} [Field Ω] [Algebra K Ω]
    (E M : IntermediateField K Ω) (hEM : E ≤ M) [Normal K E]
    (β : Eˣ) (σ : Gal(M/K)) :
    rootQuotient (K := K) (L := M)
        (Units.map (IntermediateField.inclusion hEM).toMonoidHom β) σ =
      Units.map (IntermediateField.inclusion hEM).toMonoidHom
        (rootQuotient (K := K) (L := E) β
          (intermediateFieldRestrictNormalHom E M hEM σ)) := by
  have hcomm : IntermediateField.inclusion hEM
      (intermediateFieldRestrictNormalHom E M hEM σ (β : E)) =
      σ (IntermediateField.inclusion hEM (β : E)) := by
    apply M.val.injective
    exact intermediateFieldRestrictNormalHom_apply_val E M hEM σ β
  apply Units.ext
  simp only [rootQuotient, AlgEquiv.smul_units_def,
    Units.val_div_eq_div_val, Units.coe_map]
  calc
    σ (IntermediateField.inclusion hEM (β : E)) /
        IntermediateField.inclusion hEM (β : E) =
      IntermediateField.inclusion hEM
          (intermediateFieldRestrictNormalHom E M hEM σ (β : E)) /
        IntermediateField.inclusion hEM (β : E) :=
      congrArg (fun z : M => z / IntermediateField.inclusion hEM (β : E)) hcomm.symm
    _ = IntermediateField.inclusion hEM
      (intermediateFieldRestrictNormalHom E M hEM σ (β : E) / (β : E)) :=
      (map_div₀ (IntermediateField.inclusion hEM).toRingHom
        (intermediateFieldRestrictNormalHom E M hEM σ (β : E)) (β : E)).symm

private theorem radicalPairing_eq_simpleSymbolHom
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    radicalPairing K n hnK hmu a b = simpleSymbolHom K n hnK hmu b a := by
  let E := chosenSimpleKummerExtension K n hnK b
  let M := radicalExtension K n
  let hEM : E ≤ M := chosenSimpleKummerExtension_le_maximalKummerExtension K n hnK b
  let βE : Eˣ := chosenSimpleKummerRootUnit K n hnK b
  let βM : Mˣ := Units.map (IntermediateField.inclusion hEM).toMonoidHom βE
  let σM : Gal(M/K) := radicalArtin K n hnK hmu a
  let σE : Gal(E/K) := simpleArtin K n hnK hmu b a
  letI : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : FiniteDimensional K M :=
    maximalKummerRadicalExtension_finiteDimensional K n hnK hmu
  letI : IsAbelianGalois K M :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := SeparableClosure K) n hmu (maximalKummerSubgroup K n).1
  have hβM : βM ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom b := by
    calc
      βM ^ (n : ℕ) = Units.map (IntermediateField.inclusion hEM).toMonoidHom
          (βE ^ (n : ℕ)) := (map_pow _ βE (n : ℕ)).symm
      _ = Units.map (IntermediateField.inclusion hEM).toMonoidHom
          (Units.map (algebraMap K E).toMonoidHom b) :=
        congrArg (Units.map (IntermediateField.inclusion hEM).toMonoidHom)
          (chosenSimpleKummerRootUnit_pow K n hnK b)
      _ = Units.map (algebraMap K M).toMonoidHom b := by
        apply Units.ext
        rfl
  have hrestrict : intermediateFieldRestrictNormalHom E M hEM σM = σE := by
    change intermediateFieldRestrictNormalHom E M hEM
      (abelianLocalArtinMonoidHom K M a) = abelianLocalArtinMonoidHom K E a
    exact DFunLike.congr_fun (abelianLocalArtinMonoidHom_restrict K E M hEM) a
  have hmaxVal : Units.map (algebraMap K M).toMonoidHom
      ((radicalPairing K n hnK hmu a b : rootsOfUnity (n : ℕ) K) : Kˣ) =
      rootQuotient (K := K) (L := M) βM σM :=
    radicalPairing_map_rootQuotient K n hnK hmu a b βM hβM
  have hlocalVal : Units.map (algebraMap K E).toMonoidHom
      ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) =
      rootQuotient (K := K) (L := E) βE σE :=
    simpleSymbolHom_map_rootQuotient K n hnK hmu a b
  apply Subtype.ext
  apply (Units.map_injective (f := (algebraMap K M).toMonoidHom)
    (algebraMap K M).injective)
  calc
    _ = rootQuotient (K := K) (L := M) βM σM := hmaxVal
    _ = Units.map (IntermediateField.inclusion hEM).toMonoidHom
      (rootQuotient (K := K) (L := E) βE
        (intermediateFieldRestrictNormalHom E M hEM σM)) :=
      rootQuotient_inclusion K E M hEM βE σM
    _ = Units.map (IntermediateField.inclusion hEM).toMonoidHom
      (rootQuotient (K := K) (L := E) βE σE) := by rw [hrestrict]
    _ = Units.map (algebraMap K M).toMonoidHom
      ((simpleSymbolHom K n hnK hmu b a : rootsOfUnity (n : ℕ) K) : Kˣ) := by
      rw [← hlocalVal]
      apply Units.ext
      rfl

theorem simpleSymbolHom_mul_right
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b c : Kˣ) :
    simpleSymbolHom K n hnK hmu (b * c) a =
      simpleSymbolHom K n hnK hmu b a * simpleSymbolHom K n hnK hmu c a := by
  calc
    _ = radicalPairing K n hnK hmu a (b * c) :=
      (radicalPairing_eq_simpleSymbolHom K n hnK hmu a (b * c)).symm
    _ = radicalPairing K n hnK hmu a b * radicalPairing K n hnK hmu a c :=
      map_mul (radicalPairing K n hnK hmu a) b c
    _ = _ := congrArg₂ (· * ·)
      (radicalPairing_eq_simpleSymbolHom K n hnK hmu a b)
      (radicalPairing_eq_simpleSymbolHom K n hnK hmu a c)

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
