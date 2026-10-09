/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Localized root certificates adapted from GlobalHilbertSymbol.FinitePlaceComparison.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.ArtinLocalization
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.GeneratedExtension
import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra

/-! Compare the finite local symbol with the global radical's Artin root character. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1
open GlobalClassFieldTheory.Reciprocity

variable {F : Type} [Field F] [NumberField F]

theorem globalSixNeZero : ((six : ℕ) : F) ≠ 0 := by norm_num

abbrev globalRadical (b : Fˣ) := chosenSimpleKummerExtension F six globalSixNeZero b

def globalRootCharacter (D : FieldData F) (b : Fˣ) :
    Gal((globalRadical b)/F) →* rootsOfUnity 6 F :=
  (nthRootsSubgroupEquivRootsOfUnity F 6).toMonoidHom.comp
    ((nthRootsSubgroupEquivOfPrimitiveRoots F (globalRadical b)
        six (primitiveSixthRoots D)).symm.toMonoidHom.comp
      (chosenSimpleKummerRootCharacter F six globalSixNeZero (primitiveSixthRoots D) b))

def finiteRootCharacterOfExtension (D : FieldData F) (v : FinPlace F) (a b : Fˣ)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) (globalRadical b)) :
    rootsOfUnity 6 F := by
  letI : FiniteDimensional F (globalRadical b) :=
    chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b
  letI : IsAbelianGalois F (globalRadical b) :=
    chosenSimpleKummerExtension_isAbelianGalois F six globalSixNeZero
      (primitiveSixthRoots D) b
  exact globalRootCharacter D b
    (finitePlaceArtinMonoidHomOfExtension (K := F) (L := globalRadical b) v w
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))

def finiteRootCharacter (D : FieldData F) (v : FinPlace F) (a b : Fˣ) :
    rootsOfUnity 6 F := by
  letI : FiniteDimensional F (globalRadical b) :=
    chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b
  letI : IsAbelianGalois F (globalRadical b) :=
    chosenSimpleKummerExtension_isAbelianGalois F six globalSixNeZero
      (primitiveSixthRoots D) b
  exact globalRootCharacter D b
    (chosenFinitePlaceArtinMonoidHom (K := F) (L := globalRadical b) v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a))

private theorem globalRootCharacter_rootQuotient (D : FieldData F) (b : Fˣ)
    (σ : Gal((globalRadical b)/F)) :
    Units.map (algebraMap F (globalRadical b)).toMonoidHom
        (globalRootCharacter D b σ : Fˣ) =
      rootQuotient (K := F) (L := globalRadical b)
        (chosenSimpleKummerRootUnit F six globalSixNeZero b) σ := by
  let e := nthRootsSubgroupEquivOfPrimitiveRoots F (globalRadical b)
    six (primitiveSixthRoots D)
  exact (congrArg Subtype.val
    (e.apply_symm_apply
      (chosenSimpleKummerRootCharacter F six globalSixNeZero
        (primitiveSixthRoots D) b σ))).trans
    (congrArg Subtype.val
      (chosenSimpleKummerRootCharacter_apply F six globalSixNeZero
        (primitiveSixthRoots D) b σ))

def localizedGlobalRoot (v : FinPlace F) (b : Fˣ)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) (globalRadical b)) :
    (LocalizedCompletion (HeightOneSpectrum.adicAbv F v) w)ˣ :=
  Units.map (AbsoluteValue.toAlgebraicLocalization
    (HeightOneSpectrum.adicAbv F v) w.1 w.2).toMonoidHom
      (chosenSimpleKummerRootUnit F six globalSixNeZero b)

private theorem localizedGlobalRoot_pow (v : FinPlace F) (b : Fˣ)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) (globalRadical b)) :
    let C := absoluteCompletion v
    let E := LocalizedCompletion (HeightOneSpectrum.adicAbv F v) w
    letI : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
    localizedGlobalRoot v b w ^ (six : ℕ) =
      Units.map (algebraMap C E).toMonoidHom
        (Units.map (algebraMap F C).toMonoidHom b) := by
  let vF := HeightOneSpectrum.adicAbv F v
  let L := globalRadical b
  let hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  letI : SMul F w.1.Completion := hF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := LocalizedCompletion vF w
  letI : Algebra vF.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  apply Units.ext
  let toE : L →+* E := AbsoluteValue.toAlgebraicLocalization vF w.1 w.2
  let βL : Lˣ := chosenSimpleKummerRootUnit F six globalSixNeZero b
  change toE (βL : L) ^ (six : ℕ) =
    algebraMap vF.Completion E (algebraMap F vF.Completion (b : F))
  calc
    _ = toE ((βL : L) ^ (six : ℕ)) := (map_pow toE _ _).symm
    _ = toE (algebraMap F L (b : F)) := congrArg toE
      (congrArg Units.val (chosenSimpleKummerRootUnit_pow F six globalSixNeZero b))
    _ = _ := AbsoluteValue.toAlgebraicLocalization_algebraMap vF w.1 w.2 (b : F)

private theorem localizedGlobalRoot_adjoin (v : FinPlace F) (b : Fˣ)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) (globalRadical b)) :
    let C := absoluteCompletion v
    let E := LocalizedCompletion (HeightOneSpectrum.adicAbv F v) w
    letI : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
    IntermediateField.adjoin C {(localizedGlobalRoot v b w : E)} = ⊤ := by
  let vF := HeightOneSpectrum.adicAbv F v
  let L := globalRadical b
  let hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  letI : SMul F w.1.Completion := hF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := LocalizedCompletion vF w
  letI : Algebra vF.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  letI : Algebra F E := localizedCompletionGlobalAlgebra vF w
  letI : SMul F E := (localizedCompletionGlobalAlgebra vF w).toSMul
  letI : IsScalarTower F vF.Completion E := localizedCompletionIsScalarTower vF w
  exact localizedCompletion_adjoin_image_eq_top_of_adjoin_eq_top vF w
    (chosenSimpleKummerRootUnit F six globalSixNeZero b : L)
    (chosenSimpleKummerExtension_adjoin_root_eq_top F six globalSixNeZero b)

theorem absoluteHilb_eq_finiteRootCharacterOfExtension (D : FieldData F)
    (v : FinPlace F) (a b : Fˣ)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) (globalRadical b)) :
    absoluteHilb D v a b = finiteRootCharacterOfExtension D v a b w := by
  let vF := HeightOneSpectrum.adicAbv F v
  let C := absoluteCompletion v
  let L := globalRadical b
  let E := LocalizedCompletion vF w
  letI : FiniteDimensional F L :=
    chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b
  letI : IsAbelianGalois F L :=
    chosenSimpleKummerExtension_isAbelianGalois F six globalSixNeZero
      (primitiveSixthRoots D) b
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  letI : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  letI : IsAbelianGalois C E := finitePlaceLocalArtinIsAbelianGalois v w
    (chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b)
  let aC := Units.map (algebraMap F C).toMonoidHom a
  let bC := Units.map (algebraMap F C).toMonoidHom b
  let x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let σL := finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w x
  let σE := abelianLocalArtinMonoidHom C E aC
  let toE : L →+* E := AbsoluteValue.toAlgebraicLocalization vF w.1 w.2
  let βL : Lˣ := chosenSimpleKummerRootUnit F six globalSixNeZero b
  let βE : Eˣ := localizedGlobalRoot v b w
  have hlocalC : Units.map (algebraMap F C).toMonoidHom
      (absoluteHilb D v a b : Fˣ) =
      ((simpleSymbolHom C six (absoluteCompletionSixNeZero v)
        (absoluteCompletionPrimitiveRoots D v) bC aC : rootsOfUnity 6 C) : Cˣ) :=
    congrArg Subtype.val ((absoluteRootEquiv D v).apply_symm_apply _)
  have hlocalE : Units.map (algebraMap C E).toMonoidHom
      (Units.map (algebraMap F C).toMonoidHom (absoluteHilb D v a b : Fˣ)) =
      rootQuotient (K := C) (L := E) βE σE := by
    exact (congrArg (Units.map (algebraMap C E).toMonoidHom) hlocalC).trans
      (simpleSymbolHom_in_generated_extension C E six
        (absoluteCompletionSixNeZero v) (absoluteCompletionPrimitiveRoots D v)
        aC bC βE (localizedGlobalRoot_pow v b w) (localizedGlobalRoot_adjoin v b w))
  have hglobalL : Units.map (algebraMap F L).toMonoidHom
      (finiteRootCharacterOfExtension D v a b w : Fˣ) =
      rootQuotient (K := F) (L := L) βL σL :=
    globalRootCharacter_rootQuotient D b σL
  have haction : σE (toE (βL : L)) = toE (σL (βL : L)) := by
    have h := localGlobalArtin_localized_action (F := F) v w x (βL : L)
    rw [show x = Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a from rfl,
      localArtinInput_globalUnit v a] at h
    exact h
  have hglobalE : Units.map (algebraMap C E).toMonoidHom
      (Units.map (algebraMap F C).toMonoidHom
        (finiteRootCharacterOfExtension D v a b w : Fˣ)) =
      rootQuotient (K := C) (L := E) βE σE := by
    calc
      _ = Units.map toE.toMonoidHom
          (Units.map (algebraMap F L).toMonoidHom
            (finiteRootCharacterOfExtension D v a b w : Fˣ)) := by
        apply Units.ext
        exact (AbsoluteValue.toAlgebraicLocalization_algebraMap vF w.1 w.2 _).symm
      _ = Units.map toE.toMonoidHom (rootQuotient (K := F) (L := L) βL σL) :=
        congrArg (Units.map toE.toMonoidHom) hglobalL
      _ = rootQuotient (K := C) (L := E) βE σE := by
        apply Units.ext
        simp only [rootQuotient, Units.val_div_eq_div_val, Units.coe_map]
        change toE (σL (βL : L) / (βL : L)) =
          σE (toE (βL : L)) / toE (βL : L)
        rw [map_div₀, haction]
  apply Subtype.ext
  apply Units.ext
  apply ((algebraMap C E).comp (algebraMap F C)).injective
  exact congrArg Units.val (hlocalE.trans hglobalE.symm)

theorem hilbert_global_root_comparison (D : FieldData F) (v : FinPlace F) (a b : Fˣ) :
    hilb D v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b) =
        finiteRootCharacter D v a b := by
  letI : FiniteDimensional F (globalRadical b) :=
    chosenSimpleKummerExtension_finiteDimensional F six globalSixNeZero b
  letI : IsAbelianGalois F (globalRadical b) :=
    chosenSimpleKummerExtension_isAbelianGalois F six globalSixNeZero
      (primitiveSixthRoots D) b
  exact (hilbert_completion_comparison D v a b).trans
    (absoluteHilb_eq_finiteRootCharacterOfExtension D v a b
      (chosenFinitePlaceExtension (L := globalRadical b) v))

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
