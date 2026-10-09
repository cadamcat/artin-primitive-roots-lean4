/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from GlobalHilbertSymbol.FinitePlaceLocalGlobal and
GlobalHilbertSymbol.FinitePlaceCharacterComparison.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.CompletionComparison
import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization

/-! Compatibility of the actual finite local and global Artin actions. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory LocalClassFieldTheory
open AlgebraicNumberTheory.Valuations HilbertRamification
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1
open GlobalClassFieldTheory.Reciprocity

variable {F : Type} [Field F] [NumberField F]

theorem localArtinInput_globalUnit (v : FinPlace F) (a : Fˣ) :
    finitePlaceLocalArtinInput v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) =
      Units.map (algebraMap F (absoluteCompletion v)).toMonoidHom a := by
  apply Units.ext
  apply (finitePlaceCompletionRingEquiv v).injective
  let x : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  have hleft : finitePlaceCompletionRingEquiv v
      (finitePlaceLocalArtinInput v x : absoluteCompletion v) =
      (x : v.adicCompletion F) :=
    congrArg Units.val ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply x)
  calc
    finitePlaceCompletionRingEquiv v
        (finitePlaceLocalArtinInput v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) :
          absoluteCompletion v) = (x : v.adicCompletion F) := hleft
    _ = algebraMap F (v.adicCompletion F) (a : F) := rfl
    _ = finitePlaceCompletionRingEquiv v
        (Units.map (algebraMap F (absoluteCompletion v)).toMonoidHom a :
          absoluteCompletion v) := by
      change algebraMap F (v.adicCompletion F) (a : F) =
        finitePlaceCompletionRingEquiv v (algebraMap F (absoluteCompletion v) (a : F))
      rw [finitePlaceCompletionRingEquiv_eq_relative]
      exact (relativeFinitePlaceCompletionAlgEquiv v).commutes (a : F) |>.symm

theorem localGlobalArtin_localized_action
    {L : Type} [Field L] [Algebra F L]
    [hFLfinite : FiniteDimensional F L] [IsAbelianGalois F L]
    (v : FinPlace F)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv F v) L)
    (x : (v.adicCompletion F)ˣ) (z : L) :
    let vF := HeightOneSpectrum.adicAbv F v
    let E := LocalizedCompletion vF w
    letI : Algebra vF.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    (@abelianLocalArtinMonoidHom vF.Completion E
      (inferInstance : Field vF.Completion) (inferInstance : Field E)
      (finitePlaceLocalArtinLocalizedAlgebra v w)
      (finitePlaceLocalArtinCompletionValuativeRel v)
      (inferInstance : TopologicalSpace vF.Completion)
      (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
      (finitePlaceLocalArtinFiniteDimensional v w)
      (finitePlaceLocalArtinIsAbelianGalois v w hFLfinite)
      (finitePlaceLocalArtinInput v x))
        (AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 z) =
      AbsoluteValue.toAlgebraicLocalization vF w.1 w.2
        ((finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w x) z) := by
  let vF := HeightOneSpectrum.adicAbv F v
  let E := LocalizedCompletion vF w
  letI : Algebra vF.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  let σE := @abelianLocalArtinMonoidHom vF.Completion E
    (inferInstance : Field vF.Completion) (inferInstance : Field E)
    (finitePlaceLocalArtinLocalizedAlgebra v w)
    (finitePlaceLocalArtinCompletionValuativeRel v)
    (inferInstance : TopologicalSpace vF.Completion)
    (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
    (finitePlaceLocalArtinFiniteDimensional v w)
    (finitePlaceLocalArtinIsAbelianGalois v w hFLfinite)
    (finitePlaceLocalArtinInput v x)
  let σG := finitePlaceArtinMonoidHomOfExtension (K := F) (L := L) v w x
  have hfactor := finitePlaceArtinMonoidHomOfExtension_apply_normalized
    (K := F) (L := L) v w x
  let hvF : vF.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let eD : absoluteValueDecompositionGroup F w.1 ≃* Gal(E/vF.Completion) :=
    decompositionGroupEquivAlgebraicLocalizationAut vF hvF w
  let δ : absoluteValueDecompositionGroup F w.1 := eD.symm σE
  have hδ : eD δ = σE := eD.apply_symm_apply σE
  change σE (AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 z) =
    AbsoluteValue.toAlgebraicLocalization vF w.1 w.2 (σG z)
  dsimp only [σG]
  rw [hfactor, ← hδ]
  exact localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    vF hvF w δ z

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
