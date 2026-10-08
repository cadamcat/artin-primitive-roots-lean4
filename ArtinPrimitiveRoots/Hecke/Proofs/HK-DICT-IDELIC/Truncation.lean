import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain
open Classical
open scoped RestrictedProduct NumberField AdeleRing FiniteAdeleRing

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.hk_misc_p

variable {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
variable [∀ i, TopologicalSpace (G i)] [∀ i, One (G i)]

theorem tendsto_restrictedProduct_truncate (hA : ∀ i, (1 : G i) ∈ A i)
    (x : Πʳ i, [G i, A i]) :
    Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact s.finite_toSet.compl_mem_cofinite] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) atTop
      (@nhds (Πʳ i, [G i, A i]) (RestrictedProduct.topologicalSpace G A cofinite) x) := by
  classical
  letI : TopologicalSpace (Πʳ i, [G i, A i]) :=
    RestrictedProduct.topologicalSpace G A cofinite
  let S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  let xS : Πʳ i, [G i, A i]_[𝓟 S] := ⟨x, by
    rw [eventually_principal]
    intro i hi
    simpa [S] using hi⟩
  have hconvPi : Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : ∀ i, G i)) := by
    apply tendsto_pi_nhds.2
    intro i
    have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s := by
      exact eventually_atTop.2 ⟨{i}, fun s hs => Finset.singleton_subset_iff.mp hs⟩
    have heq : (fun s : Finset ι => if i ∈ s then xS i else 1) =ᶠ[atTop]
        fun _ => xS i := by
      filter_upwards [hi] with s hs
      simp [hs]
    exact tendsto_const_nhds.congr' heq.symm
  let truncS (s : Finset ι) : Πʳ i, [G i, A i]_[𝓟 S] := ⟨
    fun i => if i ∈ s then xS i else 1, by
      rw [eventually_principal]
      intro i hi
      change x i ∈ A i at hi
      by_cases his : i ∈ s
      · simp [his]
        change (xS : ∀ i, G i) i ∈ A i
        simpa [xS] using hi
      · simp [his, hA i]⟩
  have hprincipal : Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : ∀ i, G i)) := hconvPi
  have htruncS : Tendsto truncS atTop
      (@nhds (Πʳ i, [G i, A i]_[𝓟 S])
        (RestrictedProduct.topologicalSpace G A (𝓟 S)) xS) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := A)
      (S := S)).tendsto_nhds_iff.mpr
    exact hprincipal
  have hinc : Tendsto (RestrictedProduct.inclusion G A hS ∘ truncS) atTop
      (𝓝 (RestrictedProduct.inclusion G A hS xS)) :=
    (RestrictedProduct.continuous_inclusion (R := G) (A := A) hS).continuousAt.tendsto
      |>.comp htruncS
  have hx : RestrictedProduct.inclusion G A hS xS = x := rfl
  have hfun : (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact s.finite_toSet.compl_mem_cofinite] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) =
      RestrictedProduct.inclusion G A hS ∘ truncS := by
    funext s
    apply Subtype.ext
    rfl
  rw [hfun, ← hx]
  exact hinc

variable {K : Type*} [Field K] [NumberField K]

private def d2FiniteSupportTrunc (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v => if v ∈ S then Dictionary.ideleFiniteCoord v x else 1,
    by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp [hv']⟩

def d2IdeleSupportTrunc (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IdeleGroup (𝓞 K) K :=
  (∏ w ∈ Finset.univ,
      IdeleGroup.ofCompletion (𝓞 K) K w (Dictionary.ideleInfiniteCoordUnit w x)) *
    ∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 K) K v (Dictionary.ideleFiniteCoord v x)

private theorem d2FiniteSupportTrunc_tendsto (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) => d2FiniteSupportTrunc x S)
      atTop (𝓝 ((x : AdeleRing (𝓞 K) K).2)) := by
  have h := tendsto_restrictedProduct_truncate (hA := fun v => by simp)
    ((x : AdeleRing (𝓞 K) K).2)
  have hfun : (fun S : Finset (HeightOneSpectrum (𝓞 K)) => d2FiniteSupportTrunc x S) =
      fun S => (⟨fun v => if v ∈ S then Dictionary.ideleFiniteCoord v x else 1,
        by
          filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
          have hv' : v ∉ S := by simpa using hv
          simp [hv']⟩ : FiniteAdeleRing (𝓞 K) K) := by
    funext S
    apply Subtype.ext
    rfl
  rw [hfun]
  exact h

private theorem d2IdeleSupportTrunc_infiniteCoord (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : InfinitePlace K) :
    Dictionary.ideleInfiniteCoord w (d2IdeleSupportTrunc x S) =
      Dictionary.ideleInfiniteCoord w x := by
  change ((Dictionary.ideleInfiniteCoordUnit w (d2IdeleSupportTrunc x S) : w.Completionˣ) :
    w.Completion) = _
  rw [d2IdeleSupportTrunc, map_mul, Dictionary.ideleInfiniteCoordUnit_finsetProduct]
  simp [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]

private theorem d2IdeleSupportTrunc_finiteCoord (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    (((d2IdeleSupportTrunc x S : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v) =
      d2FiniteSupportTrunc x S v := by
  classical
  have hcoord : Dictionary.ideleFiniteCoord v (d2IdeleSupportTrunc x S) =
      if v ∈ S then Dictionary.ideleFiniteCoord v x else 1 := by
    change Dictionary.ideleFiniteCoord v
      ((∏ w ∈ Finset.univ,
          IdeleGroup.ofCompletion (𝓞 K) K w (Dictionary.ideleInfiniteCoordUnit w x)) *
        ∏ v' ∈ S, IdeleGroup.ofAdicCompletion (𝓞 K) K v'
          (Dictionary.ideleFiniteCoord v' x)) = _
    rw [map_mul]
    have harch : Dictionary.ideleFiniteCoord v
        (∏ w ∈ Finset.univ,
          IdeleGroup.ofCompletion (𝓞 K) K w (Dictionary.ideleInfiniteCoordUnit w x)) = 1 := by
      rw [map_prod]
      simp [Dictionary.ideleFiniteCoord_ofCompletion]
    have hfin := Dictionary.ideleFiniteCoord_finsetProduct v S
      (fun v' => Dictionary.ideleFiniteCoord v' x)
    rw [harch, hfin]
    simp
  calc
    ((d2IdeleSupportTrunc x S : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v =
        ((Dictionary.ideleFiniteCoord v (d2IdeleSupportTrunc x S) : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) :=
      (Dictionary.ideleFiniteCoord_apply v (d2IdeleSupportTrunc x S)).symm
    _ = if v ∈ S then
          ((Dictionary.ideleFiniteCoord v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)
        else 1 := by
          rw [hcoord]
          split_ifs <;> simp
    _ = d2FiniteSupportTrunc x S v := rfl

private theorem d2IdeleSupportTrunc_coe (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (d2IdeleSupportTrunc x S : AdeleRing (𝓞 K) K) =
      ((x : AdeleRing (𝓞 K) K).1, d2FiniteSupportTrunc x S) := by
  apply Prod.ext
  · funext w
    exact d2IdeleSupportTrunc_infiniteCoord x S w
  · ext v
    exact congrArg (fun z : v.adicCompletion K => z.toCompletion)
      (d2IdeleSupportTrunc_finiteCoord x S v)

private theorem d2IdeleSupportTrunc_inv (x : IdeleGroup (𝓞 K) K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (d2IdeleSupportTrunc x S)⁻¹ = d2IdeleSupportTrunc x⁻¹ S := by
  classical
  simp [d2IdeleSupportTrunc, map_inv, Finset.prod_inv_distrib]
  ac_rfl

private theorem d2IdeleSupportTrunc_coe_tendsto (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      (d2IdeleSupportTrunc x S : AdeleRing (𝓞 K) K)) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K))) := by
  have hprod : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ((x : AdeleRing (𝓞 K) K).1, d2FiniteSupportTrunc x S)) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K).1, (x : AdeleRing (𝓞 K) K).2)) :=
    (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, d2FiniteSupportTrunc_tendsto x⟩
  have hfun : (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      (d2IdeleSupportTrunc x S : AdeleRing (𝓞 K) K)) =
      fun S => ((x : AdeleRing (𝓞 K) K).1, d2FiniteSupportTrunc x S) :=
    funext (d2IdeleSupportTrunc_coe x)
  rw [hfun]
  exact hprod

theorem tendsto_d2IdeleSupportTrunc (x : IdeleGroup (𝓞 K) K) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) => d2IdeleSupportTrunc x S)
      atTop (𝓝 x) := by
  classical
  have hval := d2IdeleSupportTrunc_coe_tendsto x
  have hvalInv : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      (((d2IdeleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) atTop
      (𝓝 ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) := by
    simpa only [d2IdeleSupportTrunc_inv] using d2IdeleSupportTrunc_coe_tendsto (x⁻¹)
  have hvalInvOp : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      MulOpposite.op (((d2IdeleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) :
        AdeleRing (𝓞 K) K)) atTop
      (𝓝 (MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K))) :=
    (MulOpposite.opHomeomorph.continuous.tendsto
      ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).comp hvalInv
  have hEmbed : Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      Units.embedProduct (AdeleRing (𝓞 K) K) (d2IdeleSupportTrunc x S)) atTop
      (𝓝 (Units.embedProduct (AdeleRing (𝓞 K) K) x)) := by
    change Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) =>
      ((d2IdeleSupportTrunc x S : AdeleRing (𝓞 K) K),
        MulOpposite.op (((d2IdeleSupportTrunc x S)⁻¹ : IdeleGroup (𝓞 K) K) :
          AdeleRing (𝓞 K) K))) atTop
      (𝓝 ((x : AdeleRing (𝓞 K) K),
        MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)))
    rw [Prod.tendsto_iff]
    exact ⟨hval, hvalInvOp⟩
  exact (Units.isEmbedding_embedProduct (M := AdeleRing (𝓞 K) K)).tendsto_nhds_iff.mpr hEmbed

end ArtinPrimitiveRoots.Proofs.hk_misc_p
