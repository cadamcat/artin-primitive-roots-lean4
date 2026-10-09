/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Valuation compatibility adapted from FinitePlaceAdicLocalField.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Semilinear
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction

/-! Comparison of the adic and absolute-value completion symbols on global units. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory LocalFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1
open GlobalClassFieldTheory.Reciprocity

variable {F : Type} [Field F] [NumberField F]

abbrev absoluteCompletion (v : FinPlace F) := (HeightOneSpectrum.adicAbv F v).Completion

theorem absoluteCompletionSixNeZero (v : FinPlace F) :
    ((six : ℕ) : absoluteCompletion v) ≠ 0 := by
  intro h
  change (6 : absoluteCompletion v) = 0 at h
  have hF : (6 : F) = 0 := (algebraMap F (absoluteCompletion v)).injective
    (by simpa only [map_ofNat, map_zero] using h)
  exact (by norm_num : (6 : F) ≠ 0) hF

theorem absoluteCompletionPrimitiveRoots (D : FieldData F) (v : FinPlace F) :
    (primitiveRoots 6 (absoluteCompletion v)).Nonempty := by
  obtain ⟨ζ, hζ⟩ := primitiveSixthRoots D
  refine ⟨algebraMap F (absoluteCompletion v) ζ, (mem_primitiveRoots (by decide)).mpr ?_⟩
  exact ((mem_primitiveRoots (by decide)).mp hζ).map_of_injective
    (algebraMap F (absoluteCompletion v)).injective

def absoluteRootEquiv (D : FieldData F) (v : FinPlace F) :
    rootsOfUnity 6 F ≃* rootsOfUnity 6 (absoluteCompletion v) :=
  rootsOfUnityEquivOfPrimitiveRoots
    (algebraMap F (absoluteCompletion v)).injective (primitiveSixthRoots D)

def absoluteHilb (D : FieldData F) (v : FinPlace F) (a b : Fˣ) : rootsOfUnity 6 F :=
  let C := absoluteCompletion v
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  (absoluteRootEquiv D v).symm
    (simpleSymbolHom C six (absoluteCompletionSixNeZero v)
      (absoluteCompletionPrimitiveRoots D v)
      (Units.map (algebraMap F C).toMonoidHom b)
      (Units.map (algebraMap F C).toMonoidHom a))

private theorem completionValuationCompatible (v : FinPlace F) :
    letI : ValuativeRel (absoluteCompletion v) :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
    SemilinearValuationCompatible (absoluteCompletion v) (v.adicCompletion F)
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := absoluteCompletion v
  let K := v.adicCompletion F
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : ValuativeRel K := completionValuativeRel v
  letI : Algebra C K := e.toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation K)
  constructor
  intro x y
  change ValuativeRel.valuation C x ≤ ValuativeRel.valuation C y ↔
    ValuativeRel.valuation K (e x) ≤ ValuativeRel.valuation K (e y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  change ‖x‖₊ ≤ ‖y‖₊ ↔
    (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (e x) ≤ Valued.v (e y)
  rw [← Valued.toNormedField.norm_le_iff]
  change ‖x‖ ≤ ‖y‖ ↔ ‖relativeFinitePlaceCompletionRingEquiv v x‖ ≤
    ‖relativeFinitePlaceCompletionRingEquiv v y‖
  rw [relativeFinitePlaceCompletionRingEquiv_norm,
    relativeFinitePlaceCompletionRingEquiv_norm]

theorem hilbert_completion_comparison (D : FieldData F) (v : FinPlace F) (a b : Fˣ) :
    hilb D v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b) =
        absoluteHilb D v a b := by
  let C := absoluteCompletion v
  let K := v.adicCompletion F
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : ValuativeRel K := completionValuativeRel v
  letI : IsNonarchimedeanLocalField K := completionIsLocalField v
  let aC := Units.map (algebraMap F C).toMonoidHom a
  let bC := Units.map (algebraMap F C).toMonoidHom b
  let aK := Units.map (algebraMap F K).toMonoidHom a
  let bK := Units.map (algebraMap F K).toMonoidHom b
  have hunit (x : Fˣ) :
      Units.map e.toMonoidHom (Units.map (algebraMap F C).toMonoidHom x) =
        Units.map (algebraMap F K).toMonoidHom x := by
    apply Units.ext
    exact (relativeFinitePlaceCompletionAlgEquiv v).commutes (x : F)
  have htransport : Units.map e.toMonoidHom
      ((simpleSymbolHom C six (absoluteCompletionSixNeZero v)
        (absoluteCompletionPrimitiveRoots D v) bC aC : rootsOfUnity 6 C) : Cˣ) =
      ((simpleSymbolHom K six (completionSixNeZero v)
        (completionPrimitiveRoots D v) bK aK : rootsOfUnity 6 K) : Kˣ) := by
    have h := simpleSymbolHom_semilinear C K e (completionValuationCompatible v)
      six (absoluteCompletionSixNeZero v) (completionSixNeZero v)
      (absoluteCompletionPrimitiveRoots D v) (completionPrimitiveRoots D v) aC bC
    rw [hunit b, hunit a] at h
    exact h
  have hadic : ((rootEquiv D v (hilb D v aK bK) : rootsOfUnity 6 K) : Kˣ) =
      ((simpleSymbolHom K six (completionSixNeZero v)
        (completionPrimitiveRoots D v) bK aK : rootsOfUnity 6 K) : Kˣ) :=
    congrArg Subtype.val ((rootEquiv D v).apply_symm_apply _)
  have habsolute :
      ((absoluteRootEquiv D v (absoluteHilb D v a b) : rootsOfUnity 6 C) : Cˣ) =
      ((simpleSymbolHom C six (absoluteCompletionSixNeZero v)
        (absoluteCompletionPrimitiveRoots D v) bC aC : rootsOfUnity 6 C) : Cˣ) :=
    congrArg Subtype.val ((absoluteRootEquiv D v).apply_symm_apply _)
  have hroot (z : rootsOfUnity 6 F) : Units.map e.toMonoidHom
      ((absoluteRootEquiv D v z : rootsOfUnity 6 C) : Cˣ) =
      ((rootEquiv D v z : rootsOfUnity 6 K) : Kˣ) := by
    apply Units.ext
    change e (algebraMap F C ((z : Fˣ) : F)) = algebraMap F K ((z : Fˣ) : F)
    exact (relativeFinitePlaceCompletionAlgEquiv v).commutes _
  apply (rootEquiv D v).injective
  apply Subtype.ext
  exact hadic.trans (htransport.symm.trans
    ((congrArg (Units.map e.toMonoidHom) habsolute.symm).trans (hroot _)))

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
