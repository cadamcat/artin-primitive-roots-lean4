import ArtinPrimitiveRoots.Hecke.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Support for primitive ray-class characters

The ray-congruence and transition-map arguments below adapt the copied
ClassFieldTheory ray-class definitions in `Hecke/RayClassCopy.lean` (Apache-2.0).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory ArtinPrimitiveRoots.Hecke

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

variable {F : Type} [Field F] [NumberField F]

private def rayCongruentUnits (m : RayClassModulus F) : Subgroup (Fˣ) where
  carrier := {x | IsRayCongruent m x}
  one_mem' := by
    constructor
    · intro v hv
      exact (rayLocalHigherUnitGroup v (m.finitePart v)).one_mem
    · intro w hw
      simp
  mul_mem' {x y} hx hy := by
    constructor
    · intro v hv
      simpa [IsRayCongruent, finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).mul_mem (hx.1 v hv) (hy.1 v hv)
    · intro w hw
      simpa [IsRayCongruent] using mul_pos (hx.2 w hw) (hy.2 w hw)
  inv_mem' {x} hx := by
    constructor
    · intro v hv
      simpa [IsRayCongruent, finitePlaceUnitEmbedding] using
        (rayLocalHigherUnitGroup v (m.finitePart v)).inv_mem (hx.1 v hv)
    · intro w hw
      simpa [IsRayCongruent] using inv_pos.mpr (hx.2 w hw)

private def rayPrincipalIdealHom (m : RayClassModulus F) :
    rayCongruentUnits m →* NumberFieldFractionalIdealGroup F :=
  (toPrincipalIdeal (𝓞 F) F).comp (rayCongruentUnits m).subtype

private theorem rayPrincipalIdealSubgroup_eq_range (m : RayClassModulus F) :
    rayPrincipalIdealSubgroup m = (rayPrincipalIdealHom m).range := by
  have hset :
      {I : NumberFieldFractionalIdealGroup F |
        ∃ x : Fˣ, IsRayCongruent m x ∧ toPrincipalIdeal (𝓞 F) F x = I} =
        Set.range (rayPrincipalIdealHom m) := by
    ext I
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hrange : Set.range (rayPrincipalIdealHom m) =
      ((rayPrincipalIdealHom m).range : Set _) := by
    ext I
    simp [MonoidHom.mem_range]
  calc
    rayPrincipalIdealSubgroup m =
        Subgroup.closure (Set.range (rayPrincipalIdealHom m)) := by
      rw [rayPrincipalIdealSubgroup, hset]
    _ = (rayPrincipalIdealHom m).range := by
      rw [hrange, Subgroup.closure_eq]

private theorem rayLocalHigherUnitGroup_antitone (v : HeightOneSpectrum (𝓞 F)) {n e : ℕ}
    (hne : n ≤ e) : rayLocalHigherUnitGroup v e ≤ rayLocalHigherUnitGroup v n := by
  intro u hu
  rcases Subgroup.mem_map.mp hu with ⟨y, hy, huy⟩
  apply Subgroup.mem_map.mpr
  refine ⟨y, ?_, huy⟩
  have hker : rayLocalHigherUnitMap v e y = 1 := by
    simpa only [MonoidHom.mem_ker] using hy
  let z : v.adicCompletionIntegers F :=
    ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y :
      (v.adicCompletionIntegers F).toSubmonoidˣ).1
  have hval : Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ e)
        z = 1 := by
    have hker' : Units.map
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ e)).toMonoidHom
        ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y) = 1 := by
      simpa [rayLocalHigherUnitMap] using hker
    have hval' := congrArg Units.val hker'
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ e) z = 1 at hval'
    exact hval'
  have hsubE :
      z - (1 : v.adicCompletionIntegers F) ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ e := by
    rw [← Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact hval
  have hsub :
      z - (1 : v.adicCompletionIntegers F) ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n :=
    (Ideal.pow_le_pow_right hne) hsubE
  have hmem :
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n)
          z = 1 := by
    rw [Ideal.Quotient.mk_eq_one_iff_sub_mem]
    exact hsub
  have hkerN : rayLocalHigherUnitMap v n y = 1 := by
    change Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n)).toMonoidHom
      ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y) = 1
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n)
      z = 1
    exact hmem
  exact hkerN

private theorem rayCongruent_mono {n m : RayClassModulus F} (h : n ≤ m)
    {x : Fˣ} (hx : IsRayCongruent m x) : IsRayCongruent n x := by
  constructor
  · intro v hv
    have hv' : v ∈ m.finitePart.support :=
      Finsupp.support_mono h.1 hv
    have he : n.finitePart v ≤ m.finitePart v := h.1 v
    exact rayLocalHigherUnitGroup_antitone v he (hx.1 v hv')
  · intro v hv
    exact hx.2 v (h.2 hv)

private theorem rayPrincipalIdealSubgroup_mono {n m : RayClassModulus F} (h : n ≤ m) :
    rayPrincipalIdealSubgroup m ≤ rayPrincipalIdealSubgroup n := by
  unfold rayPrincipalIdealSubgroup
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, rfl⟩
  exact ⟨x, rayCongruent_mono h hx, rfl⟩

private theorem rayClassPrimeToIdeals_mono {n m : RayClassModulus F} (h : n ≤ m) :
    rayClassPrimeToIdeals m ≤ rayClassPrimeToIdeals n := by
  intro I hI v hv
  exact hI v (Finsupp.support_mono h.1 hv)

/-- The transition homomorphism from the ray class group of a modulus to that of a divisor. -/
noncomputable def rayClassMap {n m : RayClassModulus F} (h : n ≤ m) :
    RayClassGroup m →* RayClassGroup n :=
  QuotientGroup.map (rayPrincipalIdealSubgroupInPrimeTo m)
    (rayPrincipalIdealSubgroupInPrimeTo n)
    (Subgroup.inclusion (rayClassPrimeToIdeals_mono h)) (by
      intro I hI
      apply Subgroup.mem_comap.mpr
      exact rayPrincipalIdealSubgroup_mono h (Subgroup.mem_comap.mp hI))

@[simp]
theorem rayClassMap_apply_mk {n m : RayClassModulus F} (h : n ≤ m)
    (I : rayClassPrimeToIdeals m) :
    rayClassMap h (QuotientGroup.mk I) =
      QuotientGroup.mk (Subgroup.inclusion (rayClassPrimeToIdeals_mono h) I) := rfl

theorem rayClassMap_ker_le {n m : RayClassModulus F}
    (h : n ≤ m) (η : RayClassGroup m →* ℂˣ) (hη : FactorsThrough η n) :
    (rayClassMap h).ker ≤ η.ker := by
  intro c hc
  obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective
    (rayPrincipalIdealSubgroupInPrimeTo m) c
  have hq : rayClassMap h (QuotientGroup.mk I) = 1 := MonoidHom.mem_ker.mp hc
  have hprincipal :
      Subgroup.inclusion (rayClassPrimeToIdeals_mono h) I ∈
        rayPrincipalIdealSubgroupInPrimeTo n :=
    (QuotientGroup.eq_one_iff _).mp hq
  have hprincipal' :
      ((rayClassPrimeToIdeals n).subtype
        (Subgroup.inclusion (rayClassPrimeToIdeals_mono h) I)) ∈
          rayPrincipalIdealSubgroup n :=
    Subgroup.mem_comap.mp hprincipal
  rw [rayPrincipalIdealSubgroup_eq_range n] at hprincipal'
  obtain ⟨u, hI⟩ := MonoidHom.mem_range.mp hprincipal'
  let x : Fˣ := u
  have hu : IsRayCongruent n x := u.property
  have hIeq : toPrincipalIdeal (𝓞 F) F x =
      (rayClassPrimeToIdeals m).subtype I := by
    simpa [rayPrincipalIdealHom, x] using hI
  have hIprime : toPrincipalIdeal (𝓞 F) F x ∈ rayClassPrimeToIdeals m := by
    rw [hIeq]
    exact I.property
  have hkill := hη.2 x hu hIprime
  have hclass :
      (QuotientGroup.mk I : RayClassGroup m) =
        QuotientGroup.mk ⟨toPrincipalIdeal (𝓞 F) F x, hIprime⟩ := by
    congr 1
    exact Subtype.ext hIeq.symm
  change η (QuotientGroup.mk I) = 1
  rw [hclass]
  exact hkill

/-- A character that factors through a divisor modulus extends from the transition-map image to
the whole smaller ray class group. The extension uses finite abelian character duality. -/
theorem exists_rayClassChar_of_factorsThrough {n m : RayClassModulus F}
    (h : n ≤ m) (η : RayClassGroup m →* ℂˣ) (hη : FactorsThrough η n) :
    ∃ ψ : RayClassGroup n →* ℂˣ, η = ψ.comp (rayClassMap h) := by
  classical
  let q := rayClassMap h
  let qR := q.rangeRestrict
  have hker : qR.ker ≤ η.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact rayClassMap_ker_le h η hη
  let ηR : q.range →* ℂˣ :=
    qR.liftOfSurjective q.rangeRestrict_surjective ⟨η, hker⟩
  have hηR : ηR.comp qR = η := by
    ext x
    simp [ηR, qR, MonoidHom.liftOfSurjective]
  have hexp : Monoid.exponent (RayClassGroup n) ≠ 0 :=
    Monoid.exponent_ne_zero_of_finite (G := RayClassGroup n)
  letI : NeZero ((Monoid.exponent (RayClassGroup n) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast hexp⟩
  have hrestrictSurj :
      Function.Surjective (MonoidHom.domRestrictHom q.range ℂˣ) :=
    MonoidHom.domRestrict_surjective (G := RayClassGroup n) (M := ℂ) (H := q.range)
  obtain ⟨ψ, hψ⟩ := hrestrictSurj ηR
  have hψval (y : q.range) : ψ y.1 = ηR y := by
    have := congrArg (fun g : q.range →* ℂˣ => g y) hψ
    simpa using this
  refine ⟨ψ, ?_⟩
  apply MonoidHom.ext
  intro x
  calc
    η x = ηR (qR x) := (DFunLike.congr_fun hηR x).symm
    _ = ψ (qR x) := (hψval (qR x)).symm

end ArtinPrimitiveRoots.Dictionary
