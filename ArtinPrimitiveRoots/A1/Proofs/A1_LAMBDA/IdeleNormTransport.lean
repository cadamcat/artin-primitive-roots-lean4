/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Restricted-product topology comparison adapted from ClassFieldTheory's
RestrictedProductUnitsTopology, whose shared artifact is unavailable.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.CompletionIntegers
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.Continuity
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-! Transport the prebuilt ordinary idele norm to the exact Mathlib groups.
The norm, its continuity, and its principal formula are used by
`relative_norm_data_exists`; local specifications are proved separately. -/

set_option autoImplicit false
open NumberField IsDedekindDomain Filter RestrictedProduct
open scoped Classical Topology NumberField RestrictedProduct
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

section RestrictedUnits

universe u v w

variable {ι : Type u} {R : ι → Type v}
  [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
variable {S : ι → Type w}
  [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)]
variable {B : ∀ i, S i}

def restrictedInclusionMonoidHom {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    (Πʳ i, [R i, B i]_[𝓖]) →* (Πʳ i, [R i, B i]_[𝓕]) where
  toFun := inclusion R (fun i => (B i : Set (R i))) h
  map_one' := rfl
  map_mul' _ _ := rfl

/-- At a principal filter, the algebraic equivalence of units is already a
topological group equivalence; no openness assumption is needed. -/
noncomputable def restrictedUnitsEquivPrincipal (T : Set ι) :
    (Πʳ i, [R i, B i]_[𝓟 T])ˣ ≃ₜ*
      (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) := by
  let e := unitsEquiv (B := B) (𝓕 := 𝓟 T) R
  refine { toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply (isEmbedding_coe_of_principal
      (R := fun i => (R i)ˣ)
      (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))).continuous_iff.mpr
    have hmap : Continuous
        (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T))) :=
      (continuous_coe (R := R) (A := fun i => (B i : Set (R i)))).units_map _
    have h : Continuous (fun x : (Πʳ i, [R i, B i]_[𝓟 T])ˣ =>
        ContinuousMulEquiv.piUnits
          (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T)) x)) :=
      ContinuousMulEquiv.piUnits.continuous.comp hmap
    refine h.congr ?_
    intro x
    funext i
    rfl
  · have hCoe : Topology.IsEmbedding
        (coeMonoidHom (B := B) (𝓕 := 𝓟 T) :
          (Πʳ i, [R i, B i]_[𝓟 T]) →* Π i, R i) :=
      isEmbedding_coe_of_principal
    have hEmbedding : Topology.IsEmbedding
        (Units.map (coeMonoidHom (B := B) (𝓕 := 𝓟 T))) :=
      hCoe.units_map
    apply hEmbedding.continuous_iff.mpr
    have h : Continuous (fun y :
        (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) =>
        ContinuousMulEquiv.piUnits.symm (y : Π i, (R i)ˣ)) :=
      ContinuousMulEquiv.piUnits.symm.continuous.comp continuous_coe
    refine h.congr ?_
    intro y
    apply Units.ext
    funext i
    rfl

/-- The principal-stage inclusion of ring restricted products induces an
open embedding of their unit groups when the distinguished submonoids are open. -/
theorem restrictedUnitsOpenEmbedding
    (hBopen : ∀ i, IsOpen (B i : Set (R i)))
    {T : Set ι} (hT : cofinite ≤ 𝓟 T) :
    Topology.IsOpenEmbedding (Units.map (restrictedInclusionMonoidHom (B := B) hT)) := by
  have hRing : Topology.IsOpenEmbedding
      (inclusion R (fun i => (B i : Set (R i))) hT) :=
    isOpenEmbedding_inclusion_principal hBopen hT
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hRing.continuous.units_map _)
    (Units.map_injective hRing.injective)
    (Units.isOpenMap_map hRing.injective hRing.isOpenMap)

/-- For open distinguished local submonoids, Mathlib's restricted-product
unit equivalence is an equivalence of topological groups. -/
noncomputable def restrictedUnitsContinuousMulEquiv
    (hBopen : ∀ i, IsOpen (B i : Set (R i))) :
    (Πʳ i, [R i, B i])ˣ ≃ₜ*
      (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]) := by
  let e := unitsEquiv (B := B) (𝓕 := cofinite) R
  refine { toMulEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
  · rw [continuous_iff_continuousAt]
    intro x
    let T : Set ι := {i | e x i ∈ (Submonoid.ofClass (B i)).units}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr (e x).2
    let y : Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T] :=
      ⟨(e x).1, fun i hi => hi⟩
    let x' : (Πʳ i, [R i, B i]_[𝓟 T])ˣ :=
      (restrictedUnitsEquivPrincipal (B := B) T).symm y
    have hx : Units.map (restrictedInclusionMonoidHom (B := B) hT) x' = x := by
      apply Units.ext
      apply RestrictedProduct.ext
      intro i
      rfl
    have hLocal : Continuous (fun z : (Πʳ i, [R i, B i]_[𝓟 T])ˣ =>
        e (Units.map (restrictedInclusionMonoidHom (B := B) hT) z)) := by
      have h := (continuous_inclusion (R := fun i => (R i)ˣ)
        (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ)) hT).comp
          (restrictedUnitsEquivPrincipal (B := B) T).continuous
      refine h.congr ?_
      intro z
      apply RestrictedProduct.ext
      intro i
      rfl
    rw [← hx]
    exact (restrictedUnitsOpenEmbedding (B := B) hBopen hT).continuousAt_iff.mp
      hLocal.continuousAt
  · apply (continuous_dom (R := fun i => (R i)ˣ)
      (A := fun i => ((Submonoid.ofClass (B i)).units : Set (R i)ˣ))).mpr
    intro T hT
    have h : Continuous (fun y :
        (Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓟 T]) =>
        Units.map (restrictedInclusionMonoidHom (B := B) hT)
          ((restrictedUnitsEquivPrincipal (B := B) T).symm y)) :=
      ((continuous_inclusion (R := R)
        (A := fun i => (B i : Set (R i))) hT).units_map _).comp
          (restrictedUnitsEquivPrincipal (B := B) T).symm.continuous
    refine h.congr ?_
    intro y
    apply Units.ext
    apply RestrictedProduct.ext
    intro i
    rfl


end RestrictedUnits

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]

/-- Finite restricted-product ideles with their unit-graph topology. -/
def finiteIdeleContinuousEquiv :
    FiniteIdeleGroup K ≃ₜ* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (restrictedUnitsContinuousMulEquiv
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletionIntegers K)
    (fun _ => Valued.isOpen_valuationSubring _)).symm

/-- The ordinary and Mathlib idele groups agree as topological groups. -/
def ideleContinuousEquiv :
    _root_.IdeleGroup K ≃ₜ* NumberField.IdeleGroup (𝓞 K) K := by
  let e := finiteIdeleContinuousEquiv K
  refine
    { toMulEquiv := _root_.IdeleGroup.equivAdeleRingUnits (K := K)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have h : Continuous (fun a : _root_.IdeleGroup K => (a.1, e a.2)) :=
      continuous_fst.prodMk (e.continuous.comp continuous_snd)
    exact (Homeomorph.prodUnits.symm.continuous.comp h).congr (fun _ => rfl)
  · have h : Continuous (fun a : NumberField.IdeleGroup (𝓞 K) K =>
        ((Homeomorph.prodUnits a).1, e.symm (Homeomorph.prodUnits a).2)) :=
      (Homeomorph.prodUnits.continuous.fst).prodMk
        (e.symm.continuous.comp Homeomorph.prodUnits.continuous.snd)
    exact h.congr (fun _ => rfl)

/-- The topology comparison preserves the canonical diagonal embedding. -/
theorem ideleContinuousEquiv_principal (a : Kˣ) :
    ideleContinuousEquiv K (_root_.IdeleGroup.principalIdele K a) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a := by
  exact (_root_.IdeleGroup.equivAdeleRingUnits (K := K)).apply_symm_apply _

/-- The ordinary relative norm on the frozen Mathlib idele groups. -/
def ideleNorm [Algebra K L] :
    NumberField.IdeleGroup (𝓞 L) L →* NumberField.IdeleGroup (𝓞 K) K :=
  (ideleContinuousEquiv K).toMonoidHom.comp
    ((_root_.IdeleGroup.norm K L).comp
      (ideleContinuousEquiv L).symm.toMonoidHom)

/-- The transported global norm is continuous. -/
theorem ideleNorm_continuous [Algebra K L] : Continuous (ideleNorm K L) :=
  (ideleContinuousEquiv K).continuous.comp
    ((_root_.IdeleGroup.norm_continuous K L).comp
      (ideleContinuousEquiv L).symm.continuous)

/-- The transported global norm sends principal ideles to the field norm. -/
theorem ideleNorm_principal [Algebra K L] (a : Lˣ) :
    ideleNorm K L (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K
        (Units.map (Algebra.norm K) a) := by
  rw [← ideleContinuousEquiv_principal L a]
  change ideleContinuousEquiv K (_root_.IdeleGroup.norm K L
    ((ideleContinuousEquiv L).symm
      (ideleContinuousEquiv L (_root_.IdeleGroup.principalIdele L a)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, _root_.IdeleGroup.norm_principalIdele]
  exact ideleContinuousEquiv_principal K _

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
