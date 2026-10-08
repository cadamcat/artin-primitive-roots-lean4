import ArtinPrimitiveRoots.Splitting.Proofs.«S7-EXT-ARTIN».LocalUnits
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
import Mathlib

set_option autoImplicit false
open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin

universe u v
variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

local instance integersInvPair (e : K ≃ₐ[ℚ] M) :
    RingHomInvPair (RingOfIntegers.mapRingEquiv e.toRingEquiv : 𝓞 K →+* 𝓞 M)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv).symm :=
  RingHomInvPair.of_ringEquiv _

local instance integersInvPairSymm (e : K ≃ₐ[ℚ] M) :
    RingHomInvPair ((RingOfIntegers.mapRingEquiv e.toRingEquiv).symm : 𝓞 M →+* 𝓞 K)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv) :=
  RingHomInvPair.of_ringEquiv _

def fractionalIdealCongr (e : K ≃ₐ[ℚ] M) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K ≃+*
      FractionalIdeal (nonZeroDivisors (𝓞 M)) M :=
  FractionalIdeal.ringEquivOfRingEquiv K M (RingOfIntegers.mapRingEquiv e.toRingEquiv)

def fractionalIdealUnitsCongr (e : K ≃ₐ[ℚ] M) :
    NumberFieldFractionalIdealGroup K ≃* NumberFieldFractionalIdealGroup M :=
  Units.mapEquiv (fractionalIdealCongr e).toMulEquiv

lemma fractionRingCongr_eq (e : K ≃ₐ[ℚ] M) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := M)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv) = e.toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := 𝓞 K)
  intro x
  change (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := M)
    (RingOfIntegers.mapRingEquiv e.toRingEquiv)) ((algebraMap (𝓞 K) K) x) = e (x : K)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

lemma fractionalIdealCongr_mem (e : K ≃ₐ[ℚ] M)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : K) :
    e x ∈ fractionalIdealCongr e I ↔ x ∈ I := by
  change e x ∈ Submodule.map
    (IsFractionRing.semilinearEquivOfRingEquiv K M
      (RingOfIntegers.mapRingEquiv e.toRingEquiv)).toLinearMap
        (I : Submodule (𝓞 K) K) ↔ x ∈ (I : Submodule (𝓞 K) K)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have he : e y = e x := by
      change (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := M)
        (RingOfIntegers.mapRingEquiv e.toRingEquiv)) y = e x at hxy
      rw [fractionRingCongr_eq] at hxy
      exact hxy
    exact e.injective he ▸ hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := M)
      (RingOfIntegers.mapRingEquiv e.toRingEquiv)) x = e x
    rw [fractionRingCongr_eq]
    rfl

lemma fractionalIdealCongr_coeIdeal (e : K ≃ₐ[ℚ] M) (I : Ideal (𝓞 K)) :
    fractionalIdealCongr e (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (I.map (RingOfIntegers.mapRingEquiv e.toRingEquiv) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [fractionalIdealCongr_mem, FractionalIdeal.mem_coeIdeal,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.toRingEquiv a,
      Ideal.mem_map_of_mem _ ha, rfl⟩
  · rintro ⟨b, hb, hbx⟩
    refine ⟨(RingOfIntegers.mapRingEquiv e.toRingEquiv).symm b, ?_, ?_⟩
    · exact (Ideal.symm_apply_mem_of_equiv_iff).mpr hb
    · apply e.injective
      simpa using hbx

lemma fractionalIdealCongr_prime (e : K ≃ₐ[ℚ] M) (w : HeightOneSpectrum (𝓞 K)) :
    fractionalIdealCongr e
        (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((finitePlaceCongr e w).asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M) := by
  rw [finitePlaceCongr_asIdeal, fractionalIdealCongr_coeIdeal]

lemma fractionalIdealCongr_principal (e : K ≃ₐ[ℚ] M) (x : Kˣ) :
    fractionalIdealUnitsCongr e (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 M) M (Units.mapEquiv e.toMulEquiv x) := by
  apply Units.ext
  simp only [fractionalIdealUnitsCongr, Units.coe_mapEquiv, coe_toPrincipalIdeal]
  change fractionalIdealCongr e (FractionalIdeal.spanSingleton _ (x : K)) =
    FractionalIdeal.spanSingleton _ (e (x : K))
  rw [fractionalIdealCongr, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton,
    fractionRingCongr_eq]
  rfl

lemma fractionalIdealCongr_count (e : K ≃ₐ[ℚ] M)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (W : HeightOneSpectrum (𝓞 M)) :
    FractionalIdeal.count M W (fractionalIdealCongr e I) =
      FractionalIdeal.count K ((finitePlaceCongr e).symm W) I := by
  classical
  by_cases hI : I = 0
  · simp only [hI, map_zero, FractionalIdeal.count_zero]
  let f := finitePlaceCongr e
  have hfactor : fractionalIdealCongr e I =
      ∏ᶠ W : HeightOneSpectrum (𝓞 M),
        (W.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ^
          FractionalIdeal.count K (f.symm W) I := by
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [MulEquivClass.map_finprod]
    simp_rw [map_zpow₀, fractionalIdealCongr_prime]
    simpa only [Equiv.symm_apply_apply] using
      (finprod_comp_equiv f (f := fun W : HeightOneSpectrum (𝓞 M) =>
        (W.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ^
          FractionalIdeal.count K (f.symm W) I))
  rw [hfactor]
  apply FractionalIdeal.count_finprod
  exact f.symm.injective.tendsto_cofinite (FractionalIdeal.finite_factors I)

/-- Pull back the finite modulus, imposing positivity at all real places. -/
def pullModulus (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M) : RayClassModulus K where
  finitePart := Finsupp.domCongr (finitePlaceCongr e).symm m.finitePart
  infinitePart := by
    letI := Fintype.ofFinite (RayClassRealPlace K)
    exact Finset.univ

@[simp] lemma pullModulus_finitePart (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (w : HeightOneSpectrum (𝓞 K)) :
    (pullModulus e m).finitePart w = m.finitePart (finitePlaceCongr e w) := by
  simp [pullModulus, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]

lemma primeTo_mem_iff (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (I : NumberFieldFractionalIdealGroup K) :
    fractionalIdealUnitsCongr e I ∈ rayClassPrimeToIdeals m ↔
      I ∈ rayClassPrimeToIdeals (pullModulus e m) := by
  constructor
  · intro h w hw
    have hw' : finitePlaceCongr e w ∈ m.finitePart.support := by
      simpa only [Finsupp.mem_support_iff, pullModulus_finitePart] using hw
    have h' := h (finitePlaceCongr e w) hw'
    change FractionalIdeal.count M (finitePlaceCongr e w)
      (fractionalIdealCongr e (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = 0 at h'
    simpa only [fractionalIdealCongr_count, Equiv.symm_apply_apply] using h'
  · intro h W hW
    have hw : (finitePlaceCongr e).symm W ∈ (pullModulus e m).finitePart.support := by
      simpa only [Finsupp.mem_support_iff, pullModulus_finitePart,
        Equiv.apply_symm_apply] using hW
    change FractionalIdeal.count M W
      (fractionalIdealCongr e (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) = 0
    rw [fractionalIdealCongr_count]
    exact h _ hw

lemma primeToIdeals_transport (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M) :
    Subgroup.map (fractionalIdealUnitsCongr e).toMonoidHom
      (rayClassPrimeToIdeals (pullModulus e m)) = rayClassPrimeToIdeals m := by
  ext J
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨I, hI, rfl⟩
    exact (primeTo_mem_iff e m I).mpr hI
  · intro hJ
    refine ⟨(fractionalIdealUnitsCongr e).symm J, ?_,
      (fractionalIdealUnitsCongr e).apply_symm_apply J⟩
    apply (primeTo_mem_iff e m _).mp
    simpa only [MulEquiv.apply_symm_apply] using hJ

def primeToIdealsCongr (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M) :
    rayClassPrimeToIdeals (pullModulus e m) ≃* rayClassPrimeToIdeals m :=
  ((fractionalIdealUnitsCongr e).subgroupMap
    (rayClassPrimeToIdeals (pullModulus e m))).trans
    (MulEquiv.subgroupCongr (primeToIdeals_transport e m))

@[simp] lemma primeToIdealsCongr_coe (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (I : rayClassPrimeToIdeals (pullModulus e m)) :
    (primeToIdealsCongr e m I : NumberFieldFractionalIdealGroup M) =
      fractionalIdealUnitsCongr e I := rfl

lemma primeToIdealsCongr_prime (e : K ≃ₐ[ℚ] M) (m : RayClassModulus M)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ (pullModulus e m).finitePart.support)
    (hW : finitePlaceCongr e w ∉ m.finitePart.support) :
    primeToIdealsCongr e m
        ⟨finitePrimeFractionalIdeal w,
          finitePrimeFractionalIdeal_mem_primeTo (pullModulus e m) w hw⟩ =
      ⟨finitePrimeFractionalIdeal (finitePlaceCongr e w),
        finitePrimeFractionalIdeal_mem_primeTo m _ hW⟩ := by
  apply Subtype.ext
  apply Units.ext
  exact fractionalIdealCongr_prime e w

end ArtinPrimitiveRoots.Proofs.s7sol_gamma.Artin
