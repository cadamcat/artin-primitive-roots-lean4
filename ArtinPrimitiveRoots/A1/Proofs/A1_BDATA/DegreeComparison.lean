import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.ResidueComparison
import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.CanonicalTopology
import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
import ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false
open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.LocalField
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

attribute [local instance] nativeCompletionValuativeRel nativeCompletionLocalField

local instance (v : FinPlace F) : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

set_option backward.isDefEq.respectTransparency.types false in
/-- Native and absolute-value completions have the same residue prime and scalar degree. -/
theorem nativeCompletionInvariants_eq_absoluteInvariants (w : FinPlace ℚ)
    (a : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ w) F) :
    nativeResidueCharacteristic (finitePlaceExtensionCentre (K := ℚ) (L := F) w a) =
        Rat.HeightOneSpectrum.natGenerator w ∧
      nativeCompletionDegree (finitePlaceExtensionCentre (K := ℚ) (L := F) w a) =
      letI := AbsoluteValue.completionAlgebra
        (NumberField.HeightOneSpectrum.adicAbv ℚ w) a.1 a.2
      Module.finrank (NumberField.HeightOneSpectrum.adicAbv ℚ w).Completion a.1.Completion := by
  classical
  let W := finitePlaceExtensionCentre (K := ℚ) (L := F) w a
  let p := Rat.HeightOneSpectrum.natGenerator w
  have hbelow : finitePlaceBelow (K := ℚ) W = w :=
    finitePlaceBelow_finitePlaceExtensionCentre (K := ℚ) (L := F) w a
  have hpdiv (n : ℕ) : p ∣ n ↔ (n : 𝓞 ℚ) ∈ w.asIdeal := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    simpa only [map_natCast] using
      (Ideal.apply_mem_of_equiv_iff (I := w.asIdeal)
        (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (x := (n : 𝓞 ℚ)))
  have hmem (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ (n : 𝓞 F) ∈ W.asIdeal := by
    rw [← hbelow, finitePlaceBelow_asIdeal]
    change algebraMap (𝓞 ℚ) (𝓞 F) (n : 𝓞 ℚ) ∈ W.asIdeal ↔ (n : 𝓞 F) ∈ W.asIdeal
    rw [map_natCast]
  have hqdiv (n : ℕ) : nativeResidueCharacteristic W ∣ n ↔ (n : 𝓞 F) ∈ W.asIdeal := by
    rw [nativeResidueCharacteristic_eq_ringChar, ← ringChar.spec,
      ← map_natCast (Ideal.Quotient.mk W.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  have hres : nativeResidueCharacteristic W = p := by
    apply Nat.dvd_antisymm
    · exact (hqdiv p).mpr ((hmem p).mp ((hpdiv p).mp dvd_rfl))
    · exact (hpdiv (nativeResidueCharacteristic W)).mpr
        ((hmem (nativeResidueCharacteristic W)).mpr
          ((hqdiv (nativeResidueCharacteristic W)).mp dvd_rfl))
  let C := W.adicCompletion F
  let t := (inferInstance : TopologicalSpace C)
  let ν := LocalFieldTheory.localIntegerValuation C
  let L := ofWithZeroValuation ν
  letI : Fact p.Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator w⟩
  have hres' : L.residueCharacteristic = p := hres
  have hcast (q : ℕ) [Fact q.Prime] (hq : q = p) :
      ∃ e : ℚ_[p] ≃+* ℚ_[q], Continuous e ∧ Continuous e.symm := by
    subst q
    exact ⟨RingEquiv.refl _, continuous_id, continuous_id⟩
  obtain ⟨e0, he0, he0s⟩ := hcast L.residueCharacteristic hres'
  letI : Algebra ℚ (w.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ w
  let ep := Rat.HeightOneSpectrum.adicCompletion.padicEquiv w
  let eQ := ep.toAlgEquiv.toRingEquiv.trans e0
  have heQs : Continuous eQ.symm := ep.symm.continuous.comp he0s
  let f : ℚ_[L.residueCharacteristic] →+* C :=
    (finitePlaceExtensionAdicCompletionMap ℚ F w a).comp eQ.symm.toRingHom
  have hf : @Continuous ℚ_[L.residueCharacteristic] C inferInstance t f :=
    (finitePlaceExtensionAdicCompletionMap_continuous ℚ F w a).comp heQs
  let vK := NumberField.HeightOneSpectrum.adicAbv ℚ w
  let baseE := relativeFinitePlaceCompletionRingEquiv w
  let eB : vK.Completion ≃+* ℚ_[L.residueCharacteristic] :=
    baseE.trans eQ
  let eC := finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) w a
  letI : Algebra vK.Completion a.1.Completion :=
    AbsoluteValue.completionAlgebra vK a.1 a.2
  letI : Module.Finite vK.Completion a.1.Completion :=
    completionModuleFinite vK (RayClass.adicAbv_isNontrivial w) a
  letI : MixedWithZeroValuationContext ν := mixedWithZeroValuationContext ν
  letI : Valued C (WithZero (Multiplicative ℤ)) := Valued.mk' ν
  letI : TopologicalSpace C := t
  have hcanon : @Continuous ℚ_[L.residueCharacteristic] C inferInstance t
      (algebraMap ℚ_[L.residueCharacteristic] C) :=
    canonical_qpadic_algebraMap_continuous C
  have hmap : algebraMap ℚ_[L.residueCharacteristic] C = f := by
    apply RingHom.coe_inj
    apply (Padic.denseRange_ratCast L.residueCharacteristic).equalizer hcanon hf
    funext r
    simp only [Function.comp_apply, map_ratCast]
  have hc : (algebraMap ℚ_[L.residueCharacteristic] C).comp eB.toRingHom =
      eC.toRingHom.comp (algebraMap vK.Completion a.1.Completion) := by
    rw [hmap]
    apply RingHom.ext
    intro x
    change finitePlaceExtensionAdicCompletionMap ℚ F w a
        (eQ.symm (eQ (baseE x))) = eC (algebraMap vK.Completion a.1.Completion x)
    rw [RingEquiv.symm_apply_apply]
    change eC (AbsoluteValue.completionMap vK a.1 a.2 (baseE.symm (baseE x))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  refine ⟨hres, ?_⟩
  change Module.finrank ℚ_[L.residueCharacteristic] C =
    Module.finrank vK.Completion a.1.Completion
  exact (Algebra.finrank_eq_of_equiv_equiv eB eC hc).symm

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
