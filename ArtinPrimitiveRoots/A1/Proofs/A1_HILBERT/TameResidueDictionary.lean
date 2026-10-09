/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.CompletionComparison
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import ValuedFieldTheory.Valuation.Completion.ExtensionInvariants

/-! The prime residue field and the actual residue field of its completion. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain LocalFieldTheory
open scoped Classical ValuativeRel
open GlobalClassFieldTheory.Reciprocity

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable (K : Type) [Field K] [NumberField K]

private theorem finitePlaceAdicAbv_nonarchimedeanAbsoluteValue
    (v : HeightOneSpectrum (𝓞 K)) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (HeightOneSpectrum.adicAbv K v) :=
  (AbsoluteValue.isNonarchimedean_iff_bounded_nat
    (HeightOneSpectrum.adicAbv K v)).1
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)

noncomputable def finitePlacePrimeResidueEquivLocalResidue
    (v : HeightOneSpectrum (𝓞 K)) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (𝓞 K ⧸ v.asIdeal) ≃+* 𝓀[C] := by
  let a := HeightOneSpectrum.adicAbv K v
  let ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    finitePlaceAdicAbv_nonarchimedeanAbsoluteValue K v
  let C := a.Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let V := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation a ha)
  let aC := AbsoluteValue.completionAbsoluteValue a
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean a
        ((AbsoluteValue.isNonarchimedean_iff_bounded_nat a).2 ha))
  let VC := LubinTate.Valuations.exponentialValuationSubring
    (AlgebraicNumberTheory.Valuations.absoluteValueExponentialValuation aC haC)
  let Rv := v.valuationSubringAtPrime K
  letI : IsLocalRing Rv :=
    IsLocalization.AtPrime.isLocalRing Rv v.asIdeal
  have hBase : Rv.toSubring = V := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change x ∈ v.valuationSubringAtPrime K ↔ _
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    change v.valuation K x ≤ 1 ↔ a x ≤ 1
    rw [HeightOneSpectrum.adicAbv_def]
    exact_mod_cast
      (WithZeroMulInt.toNNReal_le_one_iff
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm
  let eBase : Rv ≃+* V := RingEquiv.subringCongr hBase
  have hCompletion : VC = 𝒪[C] := by
    ext x
    rw [AlgebraicNumberTheory.Valuations.mem_absoluteValueExponentialSubring_iff]
    change ‖x‖ ≤ 1 ↔ x ∈ 𝒪[C]
    exact
      (finitePlaceCompletion_mem_integers_iff_norm_le_one
        a (HeightOneSpectrum.isNonarchimedean_adicAbv K v) x).symm
  let eCompletionRing : VC ≃+* 𝒪[C] :=
    RingEquiv.subringCongr hCompletion
  let eIdeal : (𝓞 K ⧸ v.asIdeal) ≃+* v.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap (𝓞 K ⧸ v.asIdeal) v.asIdeal.ResidueField)
      v.asIdeal.bijective_algebraMap_quotient_residueField
  let eLocalization : Localization.AtPrime v.asIdeal ≃ₐ[𝓞 K] Rv :=
    IsLocalization.algEquiv v.asIdeal.primeCompl _ _
  exact
    eIdeal |>.trans
      (IsLocalRing.ResidueField.mapEquiv eLocalization.toRingEquiv) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eBase) |>.trans
      (AlgebraicNumberTheory.Valuations.completionResidueEquiv a ha) |>.trans
      (IsLocalRing.ResidueField.mapEquiv eCompletionRing)

/-- The image of an algebraic integer in the valuation ring of a finite-place
completion. -/
noncomputable def finitePlaceIntegralCompletionElement
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    𝒪[C] := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  letI : ValuativeRel C :=
    finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact ⟨algebraMap K C (x : K), by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv K v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv K v)]
    calc
      ‖algebraMap K C (x : K)‖ =
          HeightOneSpectrum.adicAbv K v (x : K) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv K v) (x : K)
      _ ≤ 1 :=
        v.adicAbv_coe_le_one
          (HeightOneSpectrum.one_lt_absNorm_nnreal v) x⟩

/-- The finite-place integral element has the expected underlying completion
value. -/
@[simp]
theorem finitePlaceIntegralCompletionElement_coe
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (finitePlaceIntegralCompletionElement K v x : C) =
      algebraMap K C (x : K) :=
  rfl

/-- The finite-place residue equivalence sends the class of an algebraic
integer to the residue of its canonical image in the completion. -/
@[simp]
theorem finitePlacePrimeResidueEquivLocalResidue_mk
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    let C := (HeightOneSpectrum.adicAbv K v).Completion
    letI : ValuativeRel C :=
      finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    finitePlacePrimeResidueEquivLocalResidue K v
        (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue 𝒪[C]
        (finitePlaceIntegralCompletionElement K v x) := by
  simp only [finitePlacePrimeResidueEquivLocalResidue,
    finitePlaceIntegralCompletionElement, RingEquiv.trans_apply]
  rw [RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (Localization.AtPrime v.asIdeal)]
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  simp only [IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [AlgebraicNumberTheory.Valuations.completionResidueEquiv_residue]
  simp only [IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change
    algebraMap K (HeightOneSpectrum.adicAbv K v).Completion
        (((IsLocalization.algEquiv v.asIdeal.primeCompl
            (Localization.AtPrime v.asIdeal)
            (v.valuationSubringAtPrime K))
          (algebraMap (𝓞 K) (Localization.AtPrime v.asIdeal) x) :
        v.valuationSubringAtPrime K) : K) =
      algebraMap K (HeightOneSpectrum.adicAbv K v).Completion (x : K)
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) (v.valuationSubringAtPrime K)]
  rfl

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
