/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Local adaptation of Galois conjugation, extended to arithmetic Frobenius transport.
-/
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».Unramified
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt
import Mathlib

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

def galCongr {K L M N : Type*}
    [Field K] [Field L] [Algebra K L] [Field M] [Field N] [Algebra M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L)) : Gal(N/M) ≃* Gal(L/K) := by
  have hbase (x : K) : g (algebraMap K L x) = algebraMap M N (f x) :=
    RingHom.congr_fun hcomp.symm x
  have hbase' (x : M) : g.symm (algebraMap M N x) = algebraMap K L (f.symm x) := by
    apply g.injective
    rw [g.apply_symm_apply, hbase, f.apply_symm_apply]
  let forward (σ : Gal(N/M)) : Gal(L/K) :=
    AlgEquiv.ofRingEquiv
      (f := (g.trans σ.toRingEquiv).trans g.symm) (by
        intro x
        apply g.injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
        rw [hbase]
        change σ (algebraMap M N (f x)) = algebraMap M N (f x)
        exact σ.commutes (f x))
  let backward (τ : Gal(L/K)) : Gal(N/M) :=
    AlgEquiv.ofRingEquiv
      (f := (g.symm.trans τ.toRingEquiv).trans g) (by
        intro x
        apply g.symm.injective
        simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
        rw [hbase']
        change τ (algebraMap K L (f.symm x)) = algebraMap K L (f.symm x)
        exact τ.commutes (f.symm x))
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · intro σ
    ext x
    simp [forward, backward, AlgEquiv.ofRingEquiv_apply]
  · intro τ
    ext x
    simp [forward, backward, AlgEquiv.ofRingEquiv_apply]
  · intro σ τ
    ext x
    simp only [forward, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
      AlgEquiv.mul_apply, RingEquiv.apply_symm_apply]
    congr 1

lemma galCongr_apply {K L M N : Type*}
    [Field K] [Field L] [Algebra K L] [Field M] [Field N] [Algebra M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L)) (σ : Gal(N/M)) (x : L) :
    galCongr f g hcomp σ x = g.symm (σ (g x)) := by
  rfl

lemma isArithFrob_transport {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hcomp : (algebraMap S B).comp f.toRingHom =
      g.toRingHom.comp (algebraMap R A))
    (φ : A →ₐ[R] A) (ψ : B →ₐ[S] B)
    (hφ : ∀ x, g (φ x) = ψ (g x))
    (P : Ideal A) (W : Ideal B) (hPW : P = W.comap g.toRingHom)
    (hψ : ψ.IsArithFrobAt W) : φ.IsArithFrobAt P := by
  have hunder : P.under R = (W.under S).comap f.toRingHom := by
    change P.comap (algebraMap R A) = (W.comap (algebraMap S B)).comap f.toRingHom
    rw [hPW, Ideal.comap_comap, Ideal.comap_comap, hcomp]
  have hmap : W.under S = (P.under R).map f.toRingHom := by
    rw [hunder]
    exact (Ideal.map_comap_eq_self_of_equiv f (W.under S)).symm
  have hcard : Nat.card (R ⧸ P.under R) = Nat.card (S ⧸ W.under S) :=
    Nat.card_congr (Ideal.quotientEquiv (P.under R) (W.under S) f hmap).toEquiv
  intro x
  have hmem : φ x - x ^ Nat.card (R ⧸ P.under R) ∈ W.comap g.toRingHom := by
    change g (φ x - x ^ Nat.card (R ⧸ P.under R)) ∈ W
    rw [map_sub, map_pow, hφ x, hcard]
    exact hψ (g x)
  rwa [← hPW] at hmem

lemma arithmeticFrobenius_transport {K L M N : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    [IsAbelianGalois M N]
    (f : K ≃ₐ[ℚ] M) (g : L ≃ₐ[ℚ] N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L))
    (w : HeightOneSpectrum (𝓞 L))
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    galCongr f.toRingEquiv g.toRingEquiv hcomp
        (arithmeticFrobeniusAt (K := M) (finitePlaceCongr g w)) =
      arithmeticFrobeniusAt (K := K) w := by
  let W := finitePlaceCongr g w
  let σN := arithmeticFrobeniusAt (K := M) W
  let σL := galCongr f.toRingEquiv g.toRingEquiv hcomp σN
  have hsource : IsArithFrobAt (𝓞 M) σN W.asIdeal :=
    IsArithFrobAt.arithFrobAt (𝓞 M) (Gal(N/M)) W.asIdeal
  have hP : w.asIdeal = W.asIdeal.comap
      (RingOfIntegers.mapRingEquiv g.toRingEquiv).toRingHom := by
    change w.asIdeal =
      (w.asIdeal.comap (RingOfIntegers.mapRingEquiv g.toRingEquiv).symm.toRingHom).comap
        (RingOfIntegers.mapRingEquiv g.toRingEquiv).toRingHom
    rw [Ideal.comap_comap, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.comap_id]
  have hσ : IsArithFrobAt (𝓞 K) σL w.asIdeal := by
    apply isArithFrob_transport
      (RingOfIntegers.mapRingEquiv f.toRingEquiv)
      (RingOfIntegers.mapRingEquiv g.toRingEquiv)
      (integers_compatibility f.toRingEquiv g.toRingEquiv hcomp)
      (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σL)
      (MulSemiringAction.toAlgHom (𝓞 M) (𝓞 N) σN)
      ?_ w.asIdeal W.asIdeal hP hsource
    intro x
    apply Subtype.ext
    change g (galCongr f.toRingEquiv g.toRingEquiv hcomp σN (x : L)) =
      σN (g (x : L))
    rw [galCongr_apply]
    change g (g.symm (σN (g (x : L)))) = σN (g (x : L))
    exact g.apply_symm_apply _
  let : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hunram
  have hEq := hσ.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt (𝓞 K) (Gal(L/K)) w.asIdeal)
    w.asIdeal.primeCompl_le_nonZeroDivisors
  have hfield : σL.toRingHom = (arithmeticFrobeniusAt (K := K) w).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    have hx := AlgHom.congr_fun hEq x
    exact congrArg (fun y : 𝓞 L => (y : L)) hx
  ext x
  exact RingHom.congr_fun hfield x

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
