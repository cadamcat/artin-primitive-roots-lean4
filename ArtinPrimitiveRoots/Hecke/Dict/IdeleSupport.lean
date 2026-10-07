import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import ArtinPrimitiveRoots.Hecke.Dict.RestrictedProductDensity

/-! Finite-place truncations of ideles and their convergence in the idele group. -/

set_option autoImplicit false

open Filter IsDedekindDomain NumberField Topology
open Classical
open scoped NumberField AdeleRing FiniteAdeleRing

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

variable {K : Type*} [Field K] [NumberField K]

private def finiteSupportTrunc (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v => if v ∈ S then (ideleFiniteCoord v x : v.adicCompletion K) else 1,
    by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp [hv']⟩

/-- The product of the selected infinite-place components and finitely many finite components. -/
def ideleSupportTrunc (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IdeleGroup (𝓞 K) K :=
  (∏ w ∈ Finset.univ,
      IdeleGroup.ofCompletion (𝓞 K) K w (ideleInfiniteCoordUnit w x)) *
    ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 K) K v (ideleFiniteCoord v x)

private theorem ideleSupportTrunc_infiniteCoord (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : InfinitePlace K) :
    ideleInfiniteCoord w (ideleSupportTrunc x S) = ideleInfiniteCoord w x := by
  classical
  change ((ideleInfiniteCoordUnit w (ideleSupportTrunc x S) : w.Completionˣ) :
      w.Completion) = _
  simp [ideleSupportTrunc, ideleInfiniteCoordUnit_finsetProduct,
    ideleInfiniteCoordUnit_ofAdicCompletion]

private theorem ideleSupportTrunc_finiteCoord (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    (((ideleSupportTrunc x S : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v) =
      finiteSupportTrunc x S v := by
  classical
  have hcoord : ideleFiniteCoord v (ideleSupportTrunc x S) =
      if v ∈ S then ideleFiniteCoord v x else 1 := by
    simp [ideleSupportTrunc, ideleFiniteCoord_finsetProduct, ideleFiniteCoord_ofCompletion]
  rw [ideleFiniteCoord_apply, hcoord]
  simp [finiteSupportTrunc]

private theorem ideleSupportTrunc_coe (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (ideleSupportTrunc x S : AdeleRing (𝓞 K) K) =
      ((x : AdeleRing (𝓞 K) K).1, finiteSupportTrunc x S) := by
  apply Prod.ext
  · funext w
    exact ideleSupportTrunc_infiniteCoord x S w
  · ext v
    simpa using ideleSupportTrunc_finiteCoord x S v

private theorem finiteSupportTrunc_tendsto (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) => finiteSupportTrunc x S)
      atTop (𝓝 (((x : AdeleRing (𝓞 K) K).2))) := by
  simpa [finiteSupportTrunc] using
    (tendsto_restrictedProduct_truncate
      (hA := fun v => by simp)
      ((x : AdeleRing (𝓞 K) K).2))

private theorem ideleSupportTrunc_inv (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (ideleSupportTrunc x S)⁻¹ = ideleSupportTrunc x⁻¹ S := by
  classical
  simp [ideleSupportTrunc, map_inv, Finset.prod_inv_distrib]
  ac_rfl

private theorem ideleSupportTrunc_coe_tendsto (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      (ideleSupportTrunc x S : AdeleRing (𝓞 K) K)) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K))) := by
  have hprod : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ((x : AdeleRing (𝓞 K) K).1, finiteSupportTrunc x S)) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K).1, (x : AdeleRing (𝓞 K) K).2)) :=
    (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, finiteSupportTrunc_tendsto x⟩
  rw [ideleSupportTrunc_coe]
  simpa only [AdeleRing] using hprod

/-- A finite-support approximation net converges to any idele. -/
theorem tendsto_ideleSupportTrunc (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) => ideleSupportTrunc x S)
      atTop (𝓝 x) := by
  classical
  have hval := ideleSupportTrunc_coe_tendsto x
  have hvalInv : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      (((ideleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) atTop
      (𝓝 ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) := by
    simpa only [ideleSupportTrunc_inv] using
      ideleSupportTrunc_coe_tendsto (x⁻¹)
  have hvalInvOp : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      MulOpposite.op (((ideleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) :
        AdeleRing (𝓞 K) K)) atTop
      (𝓝 (MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K))) :=
    (MulOpposite.opHomeomorph.continuous.tendsto
      ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).comp hvalInv
  have hEmbed : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      Units.embedProduct (AdeleRing (𝓞 K) K) (ideleSupportTrunc x S)) atTop
      (𝓝 (Units.embedProduct (AdeleRing (𝓞 K) K) x)) := by
    change Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ((ideleSupportTrunc x S : AdeleRing (𝓞 K) K),
        MulOpposite.op (((ideleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) :
          AdeleRing (𝓞 K) K))) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K),
        MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)))
    rw [Prod.tendsto_iff]
    exact ⟨hval, hvalInvOp⟩
  exact (Units.isEmbedding_embedProduct (AdeleRing (𝓞 K) K)).tendsto_nhds_iff.mpr hEmbed

end ArtinPrimitiveRoots.Dictionary
