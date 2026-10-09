import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.TameResidueDictionary
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ResidueCompatibility

/-! Completion valuation-ring units and the residue of arbitrary global elements. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Classical ValuativeRel
open GlobalClassFieldTheory.Reciprocity
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

variable {F : Type} [Field F] [NumberField F]

theorem absoluteCompletionUnit_residue
    (v : FinPlace F) (u : Fˣ) (hu : residue v (u : F) ≠ 0) :
    let C := absoluteCompletion v
    letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
    letI : IsNonarchimedeanLocalField C :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    ∃ uO : 𝒪[C]ˣ,
      integerUnitsToFieldUnits C uO =
        Units.map (algebraMap F C).toMonoidHom u ∧
      IsLocalRing.residue 𝒪[C] (uO : 𝒪[C]) =
        finitePlacePrimeResidueEquivLocalResidue F v (residue v (u : F)) := by
  let C := absoluteCompletion v
  letI : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have huVal : v.valuation F (u : F) = 1 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one
      v (u : F)).mp hu
  let y : C := algebraMap F C (u : F)
  have hyNorm : ‖y‖ = 1 := by
    calc
      ‖y‖ = HeightOneSpectrum.adicAbv F v (u : F) :=
        AbsoluteValue.completionAbsoluteValue_coe
          (HeightOneSpectrum.adicAbv F v) (u : F)
      _ = 1 := by rw [HeightOneSpectrum.adicAbv_def, huVal]; simp
  have hyNe : y ≠ 0 := by
    intro hy
    rw [hy, norm_zero] at hyNorm
    exact zero_ne_one hyNorm
  let yIntegral : 𝒪[C] := ⟨y, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv F v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv F v)]
    exact hyNorm.le⟩
  let yInvIntegral : 𝒪[C] := ⟨y⁻¹, by
    rw [finitePlaceCompletion_mem_integers_iff_norm_le_one
      (HeightOneSpectrum.adicAbv F v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv F v),
      norm_inv, hyNorm, inv_one]⟩
  let uO : 𝒪[C]ˣ := {
    val := yIntegral
    inv := yInvIntegral
    val_inv := by
      apply Subtype.ext
      exact mul_inv_cancel₀ hyNe
    inv_val := by
      apply Subtype.ext
      exact inv_mul_cancel₀ hyNe }
  refine ⟨uO, ?_, ?_⟩
  · apply Units.ext
    rfl
  · have hFrac : ∃ ab : 𝓞 F × 𝓞 F,
        ab.2 ∉ v.asIdeal ∧
          (u : F) * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := by
      obtain ⟨n, d, hnd⟩ :=
        v.exists_primeCompl_mul_eq_of_integer (u : F) huVal.le
      exact ⟨(n, (d : 𝓞 F)), d.property, hnd⟩
    let n : 𝓞 F := hFrac.choose.1
    let d : 𝓞 F := hFrac.choose.2
    have hdNotMem : d ∉ v.asIdeal := hFrac.choose_spec.1
    have hnd : (u : F) * algebraMap (𝓞 F) F d =
        algebraMap (𝓞 F) F n := hFrac.choose_spec.2
    have hmulO : (uO : 𝒪[C]) * finitePlaceIntegralCompletionElement F v d =
        finitePlaceIntegralCompletionElement F v n := by
      apply Subtype.ext
      change algebraMap F C (u : F) * algebraMap F C (algebraMap (𝓞 F) F d) =
        algebraMap F C (algebraMap (𝓞 F) F n)
      rw [← map_mul, hnd]
    let e := finitePlacePrimeResidueEquivLocalResidue F v
    have hresMul := congrArg (IsLocalRing.residue 𝒪[C]) hmulO
    rw [map_mul, ← finitePlacePrimeResidueEquivLocalResidue_mk F v d,
      ← finitePlacePrimeResidueEquivLocalResidue_mk F v n] at hresMul
    have hdQuotNe : Ideal.Quotient.mk v.asIdeal d ≠ 0 :=
      (not_congr Ideal.Quotient.eq_zero_iff_mem).mpr hdNotMem
    have hdResidueNe : e (Ideal.Quotient.mk v.asIdeal d) ≠ 0 := by
      intro hdZero
      apply hdQuotNe
      apply e.injective
      simpa only [map_zero] using hdZero
    change IsLocalRing.residue 𝒪[C] (uO : 𝒪[C]) = e (residue v (u : F))
    rw [residue, dif_pos hFrac, map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (eq_div_iff hdResidueNe).mpr hresMul

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
