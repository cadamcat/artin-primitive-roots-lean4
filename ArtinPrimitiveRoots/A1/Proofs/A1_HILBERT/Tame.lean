import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameRootData
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Steinberg

/-! The global tame formula with the frozen unit-first orientation. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Classical ValuativeRel
open GlobalClassFieldTheory.Reciprocity
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable {F : Type} [Field F] [NumberField F]

theorem hilbert_tame_formula_H4 (D : FieldData F) :
    ∀ (v : FinPlace F), (6 : 𝓞 F) ∉ v.asIdeal → ∀ (u x : Fˣ),
      residue v (u : F) ≠ 0 →
      (((hilb D v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom u)
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom x) : Fˣ) : F)) =
        (algebraMap (𝓞 F) F (((chiAlg v (u : F)) : (𝓞 F)ˣ) : 𝓞 F)) ^
          (FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))) := by
  intro v h6 u x hu
  let C := absoluteCompletion v
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let jC : Fˣ →* Cˣ := Units.map (algebraMap F C).toMonoidHom
  let jK : Fˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
  let m : ℤ := FractionalIdeal.count F v
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))
  let zF := integralSixthRootToNthRoots (chiAlg v (u : F))
  let rF : rootsOfUnity 6 F := nthRootsSubgroupEquivRootsOfUnity F 6 zF
  let rC : rootsOfUnity 6 C :=
    nthRootsSubgroupEquivRootsOfUnity C 6 (absoluteChiRoot v u)
  obtain ⟨hn, hdvd, uO, huO, hz⟩ := absoluteCompletion_chiAlg_rootData D v h6 u hu
  have hroot : absoluteRootEquiv D v rF = rC := by
    apply Subtype.ext
    apply Units.ext
    simp only [absoluteRootEquiv,
      val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe]
    rfl
  have hlocal : simpleSymbolHom C six (absoluteCompletionSixNeZero v)
      (absoluteCompletionPrimitiveRoots D v) (jC u) (jC x) =
      rC ^ valuationMap C (Additive.ofMul (jC x)) := by
    have huO' : integerUnitsToFieldUnits C uO = jC u := huO
    change simpleSymbolHom C six (absoluteCompletionSixNeZero v)
      (absoluteCompletionPrimitiveRoots D v) (jC u) (jC x) =
      nthRootsSubgroupEquivRootsOfUnity C (six : ℕ) (absoluteChiRoot v u) ^
        valuationMap C (Additive.ofMul (jC x))
    rw [← huO']
    exact simpleSymbolHom_unit_radical C six (absoluteCompletionSixNeZero v)
      hn (absoluteCompletionPrimitiveRoots D v) hdvd uO (absoluteChiRoot v u) hz (jC x)
  have habsolute : absoluteHilb D v x u =
      rF ^ valuationMap C (Additive.ofMul (jC x)) := by
    change (absoluteRootEquiv D v).symm
      (simpleSymbolHom C six (absoluteCompletionSixNeZero v)
        (absoluteCompletionPrimitiveRoots D v) (jC u) (jC x)) = _
    rw [hlocal, ← hroot, map_zpow, MulEquiv.symm_apply_apply]
  have hxu : hilb D v (jK x) (jK u) = rF ^ (-m) := by
    rw [hilbert_completion_comparison, habsolute,
      absoluteCompletion_valuationMap_count v x]
  have hskew := (hilbert_steinberg_skew_H2 D).1 v (jK u) (jK x)
  rw [hxu] at hskew
  have hux : hilb D v (jK u) (jK x) = rF ^ m := by
    have h := eq_inv_of_mul_eq_one_left hskew
    simpa only [zpow_neg, inv_inv] using h
  have hscalar := congrArg (fun z : rootsOfUnity 6 F => ((z : Fˣ) : F)) hux
  simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val] at hscalar
  have hrF : ((rF : Fˣ) : F) =
      algebraMap (𝓞 F) F (((chiAlg v (u : F)) : (𝓞 F)ˣ) : 𝓞 F) := rfl
  rw [hrF] at hscalar
  exact hscalar

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
