import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».RayClasses
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
import Mathlib

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

lemma formallyUnramified_transport {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hcomp : (algebraMap S B).comp f.toRingHom =
      g.toRingHom.comp (algebraMap R A))
    (hu : Algebra.FormallyUnramified S B) : Algebra.FormallyUnramified R A := by
  let : Algebra R S := f.toRingHom.toAlgebra
  let : Algebra R B := ((algebraMap S B).comp f.toRingHom).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyUnramified S B := hu
  let : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) f.surjective
  let : Algebra.FormallyUnramified R B := Algebra.FormallyUnramified.comp R S B
  let E : A ≃ₐ[R] B :=
    AlgEquiv.ofRingEquiv (f := g) (fun x => RingHom.congr_fun hcomp.symm x)
  exact Algebra.FormallyUnramified.of_equiv E.symm

lemma unramifiedAt_transport {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hcomp : (algebraMap S B).comp f.toRingHom =
      g.toRingHom.comp (algebraMap R A))
    (P : Ideal A) [P.IsPrime] (W : Ideal B) [W.IsPrime]
    (hPW : P = W.comap g.toRingHom)
    (hu : Algebra.IsUnramifiedAt S W) : Algebra.IsUnramifiedAt R P := by
  let E := Localization.localRingEquiv P W g hPW
  apply formallyUnramified_transport f E _ hu
  ext x
  change (algebraMap S (Localization.AtPrime W)) (f x) =
    E ((algebraMap R (Localization.AtPrime P)) x)
  rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply S B (Localization.AtPrime W)]
  change (algebraMap B (Localization.AtPrime W)) ((algebraMap S B) (f x)) =
    Localization.localRingHom P W g.toRingHom hPW
      ((algebraMap A (Localization.AtPrime P)) ((algebraMap R A) x))
  rw [Localization.localRingHom_to_map]
  exact congrArg (algebraMap B (Localization.AtPrime W)) (RingHom.congr_fun hcomp x)

lemma unramifiedIn_transport {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hcomp : (algebraMap S B).comp f.toRingHom =
      g.toRingHom.comp (algebraMap R A))
    (p : Ideal R)
    (hu : Algebra.IsUnramifiedIn B (p.comap f.symm.toRingHom)) :
    Algebra.IsUnramifiedIn A p := by
  have hinverse : g.symm.toRingHom.comp (algebraMap S B) =
      (algebraMap R A).comp f.symm.toRingHom := by
    ext s
    apply g.injective
    change g (g.symm ((algebraMap S B) s)) = g ((algebraMap R A) (f.symm s))
    rw [g.apply_symm_apply]
    have he := RingHom.congr_fun hcomp (f.symm s)
    change (algebraMap S B) (f (f.symm s)) = g ((algebraMap R A) (f.symm s)) at he
    simpa only [f.apply_symm_apply] using he
  intro P hP hlie
  let : P.IsPrime := hP
  let W := P.comap g.symm.toRingHom
  have hPW : P = W.comap g.toRingHom := by
    dsimp [W]
    rw [Ideal.comap_comap, RingEquiv.symm_comp, Ideal.comap_id]
  have hlieW : W.LiesOver (p.comap f.symm.toRingHom) := ⟨by
    change p.comap f.symm.toRingHom =
      (P.comap g.symm.toRingHom).comap (algebraMap S B)
    rw [Ideal.comap_comap, hinverse, ← Ideal.comap_comap]
    exact congrArg (fun I : Ideal R => I.comap f.symm.toRingHom) hlie.over⟩
  exact unramifiedAt_transport f g hcomp P W hPW (hu W inferInstance hlieW)

lemma integers_compatibility {K L M N : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L)) :
    (algebraMap (𝓞 M) (𝓞 N)).comp (RingOfIntegers.mapRingEquiv f).toRingHom =
      (RingOfIntegers.mapRingEquiv g).toRingHom.comp (algebraMap (𝓞 K) (𝓞 L)) := by
  ext x
  change (algebraMap M N) (f (x : K)) = g ((algebraMap K L) (x : K))
  exact RingHom.congr_fun hcomp (x : K)

lemma unramifiedOutside_transport {K L M N : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    (f : K ≃ₐ[ℚ] M) (g : L ≃ₐ[ℚ] N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L))
    (m : RayClassModulus M)
    (hu : ClassFieldTheory.IsUnramifiedOutsideModulus M N m) :
    ClassFieldTheory.IsUnramifiedOutsideModulus K L (pullModulus f m) := by
  constructor
  · intro v hv
    have hvM : finitePlaceCongr f v ∉ m.finitePart.support := by
      simpa only [Finsupp.mem_support_iff, pullModulus_finitePart] using hv
    exact unramifiedIn_transport
      (RingOfIntegers.mapRingEquiv f.toRingEquiv)
      (RingOfIntegers.mapRingEquiv g.toRingEquiv)
      (integers_compatibility f.toRingEquiv g.toRingEquiv hcomp)
      v.asIdeal (hu.1 (finitePlaceCongr f v) hvM)
  · intro v hv hnot
    simp [pullModulus] at hnot

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
