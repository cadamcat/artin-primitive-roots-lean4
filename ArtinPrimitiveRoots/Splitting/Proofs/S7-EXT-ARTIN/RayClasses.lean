import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».FractionalIdeals
import Mathlib

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

universe u v
variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

lemma completionCongr_unitEmbedding (e : K ≃ₐ[ℚ] M)
    (W : HeightOneSpectrum (𝓞 M)) (x : Kˣ) :
    Units.mapEquiv (completionCongr e W).toMulEquiv
        (finitePlaceUnitEmbedding ((finitePlaceCongr e).symm W) x) =
      finitePlaceUnitEmbedding W (Units.mapEquiv e.toMulEquiv x) := by
  let : Algebra K M := e.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hKM : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  apply Units.ext
  change completionCongr e W ((x : K) : w.adicCompletion K) =
    (e (x : K) : W.adicCompletion M)
  change finitePlaceAdicCompletionMap K M w ⟨W, hKM⟩
      ((x : K) : w.adicCompletion K) = _
  exact finitePlaceAdicCompletionMap_coe K M w ⟨W, hKM⟩ (x : K)

lemma ray_congruent_transport (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (x : Kˣ) (hx : IsRayCongruent (pullModulus e m) x) :
    IsRayCongruent m (Units.mapEquiv e.toMulEquiv x) := by
  constructor
  · intro W hW
    let w := (finitePlaceCongr e).symm W
    have hw : w ∈ (pullModulus e m).finitePart.support := by
      simpa only [Finsupp.mem_support_iff, pullModulus_finitePart,
        w, Equiv.apply_symm_apply] using hW
    have hxw := hx.1 w hw
    simp only [pullModulus_finitePart, w, Equiv.apply_symm_apply] at hxw
    rw [← completionCongr_unitEmbedding e W x,
      ← higher_units_transport e W (m.finitePart W)]
    exact Subgroup.mem_map.mpr ⟨_, hxw, rfl⟩
  · intro v _
    let vK := v.1.comap e.toRingHom
    have hvK : vK.IsReal := v.2.comap e.toRingHom
    have hpos := hx.2 ⟨vK, hvK⟩ (by simp [pullModulus])
    have heval : vK.embedding_of_isReal hvK (x : K) =
        v.1.embedding_of_isReal v.2 (e (x : K)) := by
      apply Complex.ofReal_injective
      simp only [InfinitePlace.embedding_of_isReal_apply]
      change (v.1.comap e.toRingHom).embedding (x : K) = v.1.embedding (e (x : K))
      rw [InfinitePlace.comap_embedding_of_isReal e.toRingHom hvK]
      rfl
    change 0 < v.1.embedding_of_isReal v.2 (e (x : K))
    exact heval ▸ hpos

lemma rayPrincipalInPrimeTo_transport (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M) :
    rayPrincipalIdealSubgroupInPrimeTo (pullModulus e m) ≤
      (rayPrincipalIdealSubgroupInPrimeTo m).comap
        (primeToIdealsCongr e m).toMonoidHom := by
  have hprincipal : rayPrincipalIdealSubgroup (pullModulus e m) ≤
      (rayPrincipalIdealSubgroup m).comap
        (fractionalIdealUnitsCongr e).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro I ⟨x, hx, rfl⟩
    change fractionalIdealUnitsCongr e (toPrincipalIdeal (𝓞 K) K x) ∈
      rayPrincipalIdealSubgroup m
    rw [fractionalIdealCongr_principal]
    exact Subgroup.subset_closure ⟨Units.mapEquiv e.toMulEquiv x,
      ray_congruent_transport e m x hx, rfl⟩
  intro I hI
  change fractionalIdealUnitsCongr e (I : NumberFieldFractionalIdealGroup K) ∈
    rayPrincipalIdealSubgroup m
  exact hprincipal hI

def rayClassTransport (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M) :
    RayClassGroup (pullModulus e m) →* RayClassGroup m :=
  QuotientGroup.map (rayPrincipalIdealSubgroupInPrimeTo (pullModulus e m))
    (rayPrincipalIdealSubgroupInPrimeTo m) (primeToIdealsCongr e m).toMonoidHom
    (rayPrincipalInPrimeTo_transport e m)

lemma rayClassTransport_surjective (e : K ≃ₐ[ℚ] M)
    (m : RayClassModulus M) : Function.Surjective (rayClassTransport e m) := by
  apply QuotientGroup.map_surjective_of_surjective
  exact QuotientGroup.mk_surjective.comp (primeToIdealsCongr e m).surjective

lemma rayClassTransport_prime (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ (pullModulus e m).finitePart.support)
    (hW : finitePlaceCongr e w ∉ m.finitePart.support) :
    rayClassTransport e m (rayClassOfFinitePrime (pullModulus e m) w hw) =
      rayClassOfFinitePrime m (finitePlaceCongr e w) hW := by
  change QuotientGroup.map _ _ (primeToIdealsCongr e m).toMonoidHom _
    (QuotientGroup.mk' _ ⟨finitePrimeFractionalIdeal w, _⟩) = _
  rw [QuotientGroup.map_mk']
  change QuotientGroup.mk' _
    (primeToIdealsCongr e m ⟨finitePrimeFractionalIdeal w, _⟩) = _
  rw [primeToIdealsCongr_prime e m w hw hW]
  rfl

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
