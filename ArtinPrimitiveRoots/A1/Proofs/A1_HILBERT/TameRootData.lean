import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameValuation
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameLocalSymbol

/-! Completion roots and residue powers for the actual global sextic residue symbol. -/

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

def integralSixthRootToNthRoots (z : rootsOfUnity 6 (𝓞 F)) :
    nthRootsSubgroup F 6 := by
  refine ⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom z.1, ?_⟩
  change Units.map (algebraMap (𝓞 F) F).toMonoidHom z.1 ^ 6 = 1
  rw [← map_pow, z.2, map_one]

def absoluteChiRoot (v : FinPlace F) (u : Fˣ) :
    nthRootsSubgroup (absoluteCompletion v) 6 :=
  nthRootsSubgroupMap F (absoluteCompletion v) 6
    (integralSixthRootToNthRoots (chiAlg v (u : F)))

theorem absoluteCompletion_chiAlg_rootData
    (D : FieldData F) (v : FinPlace F) (h6 : (6 : 𝓞 F) ∉ v.asIdeal)
    (u : Fˣ) (hu : residue v (u : F) ≠ 0) :
    let C := absoluteCompletion v
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    ValuativeRel.valuation C ((six : ℕ) : C) = 1 ∧
      (six : ℕ) ∣ Nat.card 𝓀[C] - 1 ∧
      ∃ uO : 𝒪[C]ˣ,
        integerUnitsToFieldUnits C uO =
          Units.map (algebraMap F C).toMonoidHom u ∧
        (localNthRootsReduction C six (absoluteChiRoot v u)).1 =
          residueUnitsConcreteEquiv C (integerUnitsToResidueUnits C uO) ^
            ((Nat.card 𝓀[C] - 1) / (six : ℕ)) := by
  let C := absoluteCompletion v
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let e : (𝓞 F ⧸ v.asIdeal) ≃+* 𝓀[C] :=
    finitePlacePrimeResidueEquivLocalResidue F v
  have hCard : Nat.card 𝓀[C] = Ideal.absNorm v.asIdeal := by
    calc
      Nat.card 𝓀[C] = Nat.card (𝓞 F ⧸ v.asIdeal) :=
        Nat.card_congr e.toEquiv.symm
      _ = Ideal.absNorm v.asIdeal := by
        rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  let s : Fˣ := Units.mk0 (6 : F) (by norm_num)
  have hsVal : v.valuation F (s : F) = 1 := by
    change v.valuation F (algebraMap (𝓞 F) F (6 : 𝓞 F)) = 1
    exact v.valuation_eq_one_iff_notMem.mpr h6
  have hsResidue : residue v (s : F) ≠ 0 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one
      v (s : F)).mpr hsVal
  obtain ⟨sO, hsO, _⟩ := absoluteCompletionUnit_residue v s hsResidue
  have hSixLocal : ValuativeRel.valuation C ((six : ℕ) : C) = 1 := by
    change ValuativeRel.valuation C (6 : C) = 1
    have hsMap : valuationMap C
        (Additive.ofMul (Units.map (algebraMap F C).toMonoidHom s)) = 0 := by
      rw [← hsO, valuationMap_apply]
      exact v_integerUnitsToFieldUnits C sO
    have hsRaw := valuation_eq_one_of_valuationMap_eq_zero C hsMap
    change ValuativeRel.valuation C (algebraMap F C (6 : F)) = 1 at hsRaw
    simpa only [map_ofNat] using hsRaw
  refine ⟨hSixLocal, ?_, ?_⟩
  · rw [hCard]
    exact six_dvd_absNorm_sub_one D v h6
  · obtain ⟨uO, huO, huResidue⟩ := absoluteCompletionUnit_residue v u hu
    refine ⟨uO, huO, ?_⟩
    let z := chiAlg v (u : F)
    let zC := absoluteChiRoot v u
    have hzInteger : (nthRootIntegerUnit C six zC : 𝒪[C]) =
        finitePlaceIntegralCompletionElement F v (z.1 : 𝓞 F) := by
      apply Subtype.ext
      exact congrArg Units.val
        (integerUnitsToFieldUnits_nthRootIntegerUnit C six zC)
    apply Units.ext
    change IsLocalRing.residue 𝒪[C] (nthRootIntegerUnit C six zC : 𝒪[C]) =
      IsLocalRing.residue 𝒪[C] (uO : 𝒪[C]) ^
        ((Nat.card 𝓀[C] - 1) / (six : ℕ))
    rw [hzInteger, ← finitePlacePrimeResidueEquivLocalResidue_mk F v (z.1 : 𝓞 F)]
    rw [KummerProofs.chiAlg_spec D v h6 (u : F) hu, map_pow, huResidue, hCard]
    rfl

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
