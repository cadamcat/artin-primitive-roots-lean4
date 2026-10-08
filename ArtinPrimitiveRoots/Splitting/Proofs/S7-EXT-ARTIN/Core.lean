import /- Reciprocity is prebuilt on the Mac. -/ ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».LocalUnits
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».FractionalIdeals
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».RayClasses
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».Unramified
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».Frobenius

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

lemma liesOver_transport {R S A B : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hcomp : (algebraMap S B).comp f.toRingHom =
      g.toRingHom.comp (algebraMap R A))
    (p : Ideal R) (P : Ideal A) (hlie : P.LiesOver p) :
    (P.comap g.symm.toRingHom).LiesOver (p.comap f.symm.toRingHom) := by
  have hinverse : g.symm.toRingHom.comp (algebraMap S B) =
      (algebraMap R A).comp f.symm.toRingHom := by
    ext s
    apply g.injective
    change g (g.symm ((algebraMap S B) s)) = g ((algebraMap R A) (f.symm s))
    rw [g.apply_symm_apply]
    have he := RingHom.congr_fun hcomp (f.symm s)
    change (algebraMap S B) (f (f.symm s)) = g ((algebraMap R A) (f.symm s)) at he
    simpa only [f.apply_symm_apply] using he
  constructor
  change p.comap f.symm.toRingHom =
    (P.comap g.symm.toRingHom).comap (algebraMap S B)
  rw [Ideal.comap_comap, hinverse, ← Ideal.comap_comap]
  exact congrArg (fun I : Ideal R => I.comap f.symm.toRingHom) hlie.over

lemma transport_reciprocity_data {K L M N : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]
    [Field M] [NumberField M] [Field N] [NumberField N] [Algebra M N]
    [IsAbelianGalois M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L))
    (D : ClassFieldTheory.FiniteAbelianReciprocityData M N) :
    Nonempty (ClassFieldTheory.FiniteAbelianReciprocityData K L) := by
  let fQ := f.toRatAlgEquiv
  let gQ := g.toRatAlgEquiv
  let m := pullModulus fQ D.modulus
  let A : RayClassGroup m →* Gal(L/K) :=
    (galCongr f g hcomp).toMonoidHom.comp
      (D.artin.comp (rayClassTransport fQ D.modulus))
  have hu : ClassFieldTheory.IsUnramifiedOutsideModulus K L m :=
    unramifiedOutside_transport fQ gQ hcomp D.modulus D.unramifiedOutsideModulus
  refine ⟨{
    modulus := m
    unramifiedOutsideModulus := hu
    artin := A
    artin_surjective := ?_
    artin_frobenius := ?_ }⟩
  · exact (galCongr f g hcomp).surjective.comp
      (D.artin_surjective.comp (rayClassTransport_surjective fQ D.modulus))
  · intro v hv w hlie
    have hvM : finitePlaceCongr fQ v ∉ D.modulus.finitePart.support := by
      simpa only [Finsupp.mem_support_iff, m, pullModulus_finitePart] using hv
    have hlieM : (finitePlaceCongr gQ w).asIdeal.LiesOver
        (finitePlaceCongr fQ v).asIdeal :=
      liesOver_transport (RingOfIntegers.mapRingEquiv f)
        (RingOfIntegers.mapRingEquiv g)
        (integers_compatibility f g hcomp) v.asIdeal w.asIdeal hlie
    have hw : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      hu.1 v hv w.asIdeal inferInstance hlie
    change galCongr f g hcomp
      (D.artin (rayClassTransport fQ D.modulus (rayClassOfFinitePrime m v hv))) = _
    rw [rayClassTransport_prime fQ D.modulus v hv hvM,
      D.artin_frobenius (finitePlaceCongr fQ v) hvM (finitePlaceCongr gQ w) hlieM]
    exact arithmeticFrobenius_transport fQ gQ hcomp w hw

lemma reciprocity_data {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] :
    Nonempty (ClassFieldTheory.FiniteAbelianReciprocityData K L) := by
  sorry

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
