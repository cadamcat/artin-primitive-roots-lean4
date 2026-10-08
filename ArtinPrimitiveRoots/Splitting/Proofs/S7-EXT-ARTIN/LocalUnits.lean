/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Local adaptation of finite-completion transport and higher-unit membership.
-/
import /- Use the local prebuilt CFT modules. -/ ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic
import Mathlib

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

open ClassFieldTheory

universe u v
variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

/-- The finite completion at corresponding places, viewed as a field
equivalence rather than merely a continuous map. -/
def completionCongr
    (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceCongr e).symm W).adicCompletion K ≃+*
      W.adicCompletion M := by
  letI : Algebra K M := e.toRingHom.toAlgebra
  letI : Algebra M K := e.symm.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hKM : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  have hMK : finitePlaceBelow (K := M) w = W := by
    have he : finitePlaceCongr e w = W :=
      (finitePlaceCongr e).apply_symm_apply W
    apply HeightOneSpectrum.ext
    rw [← he]
    rfl
  haveI : IsScalarTower K M K := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change x = e.symm (e x)
    exact (e.symm_apply_apply x).symm
  haveI : IsScalarTower M K M := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change x = e (e.symm x)
    exact (e.apply_symm_apply x).symm
  let f : w.adicCompletion K →+* W.adicCompletion M :=
    finitePlaceAdicCompletionMap K M w ⟨W, hKM⟩
  let g : W.adicCompletion M →+* w.adicCompletion K :=
    finitePlaceAdicCompletionMap M K W ⟨w, hMK⟩
  exact RingEquiv.ofRingHom f g
    (by
      apply RingHom.ext
      intro x
      change f (g x) = x
      rw [finitePlaceAdicCompletionMap_comp M M (M := K)
        W w W hMK hKM (finitePlaceBelow_self W) x]
      exact finitePlaceAdicCompletionMap_self_apply M W x)
    (by
      apply RingHom.ext
      intro x
      change g (f x) = x
      rw [finitePlaceAdicCompletionMap_comp K K (M := M)
        w W w hKM hMK (finitePlaceBelow_self w) x]
      exact finitePlaceAdicCompletionMap_self_apply K w x)

lemma adicMap_mapsToIntegers [Algebra K M]
    (w : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 M) // finitePlaceBelow (K := K) W = w}) :
    Set.MapsTo (finitePlaceAdicCompletionMap K M w W)
      (w.adicCompletionIntegers K : Set (w.adicCompletion K))
      (W.1.adicCompletionIntegers M : Set (W.1.adicCompletion M)) := by
  intro x hx
  letI : W.1.asIdeal.LiesOver w.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal W.2.symm⟩
  have he : w.asIdeal.ramificationIdx' W.1.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver W.1.asIdeal w.ne_bot
  change Valued.v x ≤ 1 at hx
  change Valued.v (finitePlaceAdicCompletionMap K M w W x) ≤ 1
  rw [finitePlaceAdicCompletionMap_valued K M w W x]
  exact (pow_le_one_iff he).mpr hx

lemma completionCongr_mapsToIntegers (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    Set.MapsTo (completionCongr e W)
      (((finitePlaceCongr e).symm W).adicCompletionIntegers K :
        Set (((finitePlaceCongr e).symm W).adicCompletion K))
      (W.adicCompletionIntegers M : Set (W.adicCompletion M)) := by
  letI : Algebra K M := e.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hKM : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  change Set.MapsTo (finitePlaceAdicCompletionMap K M w ⟨W, hKM⟩) _ _
  exact adicMap_mapsToIntegers w ⟨W, hKM⟩

lemma completionCongr_symm_mapsToIntegers (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    Set.MapsTo (completionCongr e W).symm
      (W.adicCompletionIntegers M : Set (W.adicCompletion M))
      (((finitePlaceCongr e).symm W).adicCompletionIntegers K :
        Set (((finitePlaceCongr e).symm W).adicCompletion K)) := by
  letI : Algebra M K := e.symm.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hMK : finitePlaceBelow (K := M) w = W := by
    have he : finitePlaceCongr e w = W := (finitePlaceCongr e).apply_symm_apply W
    apply HeightOneSpectrum.ext
    rw [← he]
    rfl
  change Set.MapsTo (finitePlaceAdicCompletionMap M K W ⟨w, hMK⟩) _ _
  exact adicMap_mapsToIntegers W ⟨w, hMK⟩

noncomputable def completionIntegersCongr (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceCongr e).symm W).adicCompletionIntegers K ≃+*
      W.adicCompletionIntegers M where
  toFun x := ⟨completionCongr e W x, completionCongr_mapsToIntegers e W x.property⟩
  invFun y := ⟨(completionCongr e W).symm y, completionCongr_symm_mapsToIntegers e W y.property⟩
  left_inv x := Subtype.ext ((completionCongr e W).symm_apply_apply x)
  right_inv y := Subtype.ext ((completionCongr e W).apply_symm_apply y)
  map_mul' x y := Subtype.ext ((completionCongr e W).map_mul x y)
  map_add' x y := Subtype.ext ((completionCongr e W).map_add x y)

/-- Membership in the `n`-th local higher-unit group is precisely the
congruence `y ≡ 1 (mod 𝔪_v^n)` for an integral-unit representative. -/
theorem mem_higherUnitGroup_iff
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K)ˣ,
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm y :
          (v.adicCompletion K)ˣ) = x ∧
        (y : v.adicCompletionIntegers K) - 1 ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  change x ∈ RayClass.localHigherUnitGroup v n ↔ _
  rw [RayClass.mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, hxy, hmap⟩
    let z : (v.adicCompletionIntegers K)ˣ :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y
    refine ⟨z, ?_, ?_⟩
    · have hback :
          (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z = y := by
        exact Equiv.symm_apply_apply _ _
      rw [hback]
      exact hxy
    · have hq : Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
          (z : v.adicCompletionIntegers K) = 1 := by
        have hv := congrArg Units.val hmap
        change Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
          (z : v.adicCompletionIntegers K) = 1 at hv
        exact hv
      exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
        (I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
        (z : v.adicCompletionIntegers K)).mp hq
  · rintro ⟨z, hz, hcong⟩
    let y : (v.adicCompletionIntegers K).units :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z
    refine ⟨y, hz, ?_⟩
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K) = 1
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
      (I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K)).mpr hcong

lemma sub_one_mem_maximal_pow_map {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A ≃+* B) (x : A) (n : ℕ) :
    f x - 1 ∈ (IsLocalRing.maximalIdeal B) ^ n ↔
      x - 1 ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  have hm : ((IsLocalRing.maximalIdeal A) ^ n).map f =
      (IsLocalRing.maximalIdeal B) ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  rw [← hm]
  simpa only [map_sub, map_one] using
    (Ideal.apply_mem_of_equiv_iff (I := (IsLocalRing.maximalIdeal A) ^ n)
      (f := f) (x := x - 1))

lemma higher_units_transport (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) (n : ℕ) :
    Subgroup.map (Units.mapEquiv (completionCongr e W).toMulEquiv).toMonoidHom
      (ClassFieldTheory.rayLocalHigherUnitGroup ((finitePlaceCongr e).symm W) n) =
        ClassFieldTheory.rayLocalHigherUnitGroup W n := by
  let w := (finitePlaceCongr e).symm W
  let Φ := completionCongr e W
  let Ψ := completionIntegersCongr e W
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (mem_higherUnitGroup_iff w n y).mp hy with ⟨z, hz, hcong⟩
    apply (mem_higherUnitGroup_iff W n _).mpr
    refine ⟨Units.mapEquiv Ψ.toMulEquiv z, ?_, ?_⟩
    · apply Units.ext
      change Φ ((z : w.adicCompletionIntegers K) : w.adicCompletion K) = Φ (y : w.adicCompletion K)
      exact congrArg Φ (congrArg Units.val hz)
    · change Ψ (z : w.adicCompletionIntegers K) - 1 ∈
        (IsLocalRing.maximalIdeal (W.adicCompletionIntegers M)) ^ n
      exact (sub_one_mem_maximal_pow_map Ψ _ n).mpr hcong
  · intro hx
    rcases (mem_higherUnitGroup_iff W n x).mp hx with ⟨z, hz, hcong⟩
    let y := Units.mapEquiv Φ.symm.toMulEquiv x
    refine ⟨y, ?_, ?_⟩
    · apply (mem_higherUnitGroup_iff w n y).mpr
      refine ⟨Units.mapEquiv Ψ.symm.toMulEquiv z, ?_, ?_⟩
      · apply Units.ext
        change Φ.symm ((z : W.adicCompletionIntegers M) : W.adicCompletion M) = Φ.symm (x : W.adicCompletion M)
        exact congrArg Φ.symm (congrArg Units.val hz)
      · change Ψ.symm (z : W.adicCompletionIntegers M) - 1 ∈
          (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K)) ^ n
        exact (sub_one_mem_maximal_pow_map Ψ.symm _ n).mpr hcong
    · apply Units.ext
      change Φ (Φ.symm (x : W.adicCompletion M)) = (x : W.adicCompletion M)
      exact Φ.apply_symm_apply _

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
