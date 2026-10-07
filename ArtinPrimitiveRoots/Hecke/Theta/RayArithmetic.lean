import ArtinPrimitiveRoots.Hecke.Theta.CFTIdealBridge
import ArtinPrimitiveRoots.Hecke.Theta.RayLocalFiniteness

/-!
# Arithmetic input for the ray theta kernel

The finite modulus ideal and the unit-invariant ray-principal indicator used by the analytic
construction.  The congruence-to-additive-residue bridge is developed below these definitions.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The integral ideal representing the finite part of a ray modulus. -/
def modulusIdeal (m : RayClassModulus K) : Ideal (𝓞 K) :=
  m.finitePart.prod (fun v e => v.asIdeal ^ e)

/-- A choice of integral ideals prime to `m`, representing each inverse ray class. -/
structure IntegralRayRepresentatives (m : RayClassModulus K) where
  ideal : RayClassGroup m → Ideal (𝓞 K)
  coprime : ∀ C, IsCoprimeTo m (ideal C)
  class_eq : ∀ C, rayClass m (ideal C) (coprime C) = C⁻¹

noncomputable def rayLocalIntegerRingHom' (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K) →+* v.adicCompletionIntegers K :=
  RingHom.codRestrict (algebraMap (𝓞 K) (v.adicCompletion K))
    (v.adicCompletionIntegers K) (fun x =>
      HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) (R := 𝓞 K) v x)

@[simp] theorem rayLocalIntegerRingHom'_coe (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    ((rayLocalIntegerRingHom' v a : v.adicCompletionIntegers K) : v.adicCompletion K) =
      algebraMap (𝓞 K) (v.adicCompletion K) a := rfl

private theorem rayCompletion_maximalIdeal_pow_iff (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ)) := by
  let val : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  haveI : val.IsRankOneDiscrete := inferInstance
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial val
  have hgen : (Valuation.IsRankOneDiscrete.generator val : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := val) (HeightOneSpectrum.valuedAdicCompletion_surjective K v)
    exact congrArg Units.val h
  have hπval : val (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    (Valuation.IsUniformizer.val hπ).trans hgen
  have hpow : val ((π ^ n : v.adicCompletionIntegers K) : v.adicCompletion K) =
      WithZero.exp (-(n : ℤ)) := by
    calc
      val ((π ^ n : v.adicCompletionIntegers K) : v.adicCompletion K) =
          val (π : v.adicCompletion K) ^ n := by simp
      _ = WithZero.exp (-1 : ℤ) ^ n := by rw [hπval]
      _ = WithZero.exp (n • (-1 : ℤ)) := by rw [← WithZero.exp_nsmul]
      _ = WithZero.exp (-(n : ℤ)) := by congr 1 <;> simp [nsmul_eq_mul]
  let x' : val.valuationSubring := x
  change x' ∈ IsLocalRing.maximalIdeal val.valuationSubring ^ n ↔
    val (x' : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ))
  rw [Valuation.IsUniformizer.is_generator hπ, Ideal.span_singleton_pow]
  change x' ∈ Ideal.span {π ^ n} ↔ val (x : v.adicCompletion K) ≤ _
  rw [Ideal.mem_span_singleton, ← hpow]
  exact Valuation.Integers.dvd_iff_le
    (Valuation.valuationSubring.integers (v := val))

private theorem rayLocalHigherUnitGroup_mem_iff (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ z : (v.adicCompletionIntegers K)ˣ,
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z :
          (v.adicCompletion K)ˣ) = x ∧
        (z : v.adicCompletionIntegers K) - 1 ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  classical
  rw [rayLocalHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    let z : (v.adicCompletionIntegers K)ˣ :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y
    refine ⟨z, ?_, ?_⟩
    · have hback : (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z = y :=
        Equiv.symm_apply_apply _ _
      rw [hback]
      exact hxy
    · have hmap := MonoidHom.mem_ker.mp hy
      have hq : Ideal.Quotient.mk
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
  · rintro ⟨z, hx, hcong⟩
    let y : (v.adicCompletionIntegers K).units :=
      (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.symm z
    refine ⟨y, ?_, hx⟩
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K) = 1
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem
      (I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)
      (z : v.adicCompletionIntegers K)).mpr hcong

private theorem mem_modulusIdeal_iff (m : RayClassModulus K) (x : 𝓞 K) :
    x ∈ modulusIdeal m ↔
      ∀ v, v ∈ m.finitePart.support → x ∈ v.asIdeal ^ m.finitePart v := by
  classical
  have hpair : (m.finitePart.support : Set (HeightOneSpectrum (𝓞 K))).Pairwise
      (fun v w => IsCoprime (v.asIdeal ^ m.finitePart v) (w.asIdeal ^ m.finitePart w)) := by
    intro v hv w hw hvw
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.pow_sup_pow_eq_top
    have hne : v.asIdeal ≠ w.asIdeal := by
      intro h
      apply hvw
      exact HeightOneSpectrum.ext h
    exact Ideal.IsMaximal.coprime_of_ne
      (v.isPrime.isMaximal v.ne_bot) (w.isPrime.isMaximal w.ne_bot) hne
  change x ∈ ∏ v ∈ m.finitePart.support, v.asIdeal ^ m.finitePart v ↔ _
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpair]
  simp

private theorem integral_ray_congruence_at_place (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 1 ≤ n) (a : 𝓞 K) (ha : a ≠ 0) :
    finitePlaceUnitEmbedding v
        (Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) ∈
        rayLocalHigherUnitGroup v n ↔ a - 1 ∈ v.asIdeal ^ n := by
  classical
  let S := v.adicCompletionIntegers K
  let aS : S := rayLocalIntegerRingHom' v a
  let x : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)
  have hval : Valued.v ((aS - 1 : S) : v.adicCompletion K) =
      v.intValuation (a - 1) := by
    have hmapSub : rayLocalIntegerRingHom' v (a - 1) = aS - 1 := by
      simp [aS]
    calc
      Valued.v ((aS - 1 : S) : v.adicCompletion K) =
          Valued.v ((rayLocalIntegerRingHom' v (a - 1) : S) : v.adicCompletion K) := by
        rw [← hmapSub]
      _ = Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) (a - 1)) := by
        rw [rayLocalIntegerRingHom'_coe]
      _ = v.valuation K (algebraMap (𝓞 K) K (a - 1)) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation
          (R := 𝓞 K) (K := K) v (a - 1)
      _ = v.intValuation (a - 1) :=
        HeightOneSpectrum.valuation_of_algebraMap (K := K) v (a - 1)
  constructor
  · intro hlocal
    obtain ⟨z, hx, hcong⟩ :=
      (rayLocalHigherUnitGroup_mem_iff v n (finitePlaceUnitEmbedding v x)).mp hlocal
    have hfield : (z : S) = aS := by
      have hv := congrArg Units.val hx
      have hcomp : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) =
          algebraMap (𝓞 K) (v.adicCompletion K) a := by
        exact (IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) a).symm
      have hv' : ((z : S) : v.adicCompletion K) =
          algebraMap (𝓞 K) (v.adicCompletion K) a := by
        simpa [finitePlaceUnitEmbedding, x] using hv.trans hcomp
      have haS : (aS : v.adicCompletion K) =
          algebraMap (𝓞 K) (v.adicCompletion K) a := rfl
      exact Subtype.val_injective (hv'.trans haS.symm)
    have hcong' : aS - 1 ∈ IsLocalRing.maximalIdeal S ^ n := by
      simpa [hfield] using hcong
    have hbound := (rayCompletion_maximalIdeal_pow_iff v n (aS - 1)).mp hcong'
    rw [hval] at hbound
    exact (v.intValuation_le_pow_iff_mem (a - 1) n).mp hbound
  · intro hideal
    have hbound : v.intValuation (a - 1) ≤ WithZero.exp (-(n : ℤ)) :=
      (v.intValuation_le_pow_iff_mem (a - 1) n).mpr hideal
    have hbound' : Valued.v ((aS - 1 : S) : v.adicCompletion K) ≤
        WithZero.exp (-(n : ℤ)) := by rw [hval]; exact hbound
    have hcong : aS - 1 ∈ IsLocalRing.maximalIdeal S ^ n :=
      (rayCompletion_maximalIdeal_pow_iff v n (aS - 1)).mpr hbound'
    have hdelta : aS - 1 ∈ IsLocalRing.maximalIdeal S :=
      (Ideal.pow_le_self (by omega : n ≠ 0)) hcong
    have haS : IsUnit aS := IsLocalRing.notMem_maximalIdeal.mp (by
      intro hmax
      have hone : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
        simpa [sub_sub] using sub_mem hmax hdelta
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
        (Ideal.eq_top_of_isUnit_mem (IsLocalRing.maximalIdeal S) hone isUnit_one))
    let z : Sˣ := haS.unit
    have hz : (z : S) = aS := haS.unit_spec
    have hx : (S.toSubmonoid.unitsEquivUnitsType.symm z :
        (v.adicCompletion K)ˣ) = finitePlaceUnitEmbedding v x := by
      apply Units.ext
      change (z : S) = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a)
      rw [hz]
      have hcomp : algebraMap (𝓞 K) (v.adicCompletion K) a =
          algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) :=
        IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) a
      change ((rayLocalIntegerRingHom' v a : S) : v.adicCompletion K) = _
      rw [rayLocalIntegerRingHom'_coe]
      exact hcomp
    have hcong' : (z : S) - 1 ∈ IsLocalRing.maximalIdeal S ^ n := by
      simpa [hz] using hcong
    apply (rayLocalHigherUnitGroup_mem_iff v n (finitePlaceUnitEmbedding v x)).mpr
    refine ⟨z, ?_, hcong'⟩
    exact hx

theorem integral_rayCongruent_iff [IsTotallyComplex K]
    (m : RayClassModulus K) (a : 𝓞 K) (ha : a ≠ 0) :
    IsRayCongruent m
      (Units.mk0 (algebraMap (𝓞 K) K a)
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) ↔
      a - 1 ∈ modulusIdeal m := by
  classical
  rw [IsRayCongruent, rayClassModulus_infinitePart_eq_empty (K := K) m]
  constructor
  · intro h
    apply (mem_modulusIdeal_iff m (a - 1)).2
    intro v hv
    have hvn : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact (integral_ray_congruence_at_place v (m.finitePart v)
      (Nat.pos_iff_ne_zero.mpr hvn) a ha).mp (h.1 v hv)
  · intro h
    constructor
    · intro v hv
      have hvn : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
      apply (integral_ray_congruence_at_place v (m.finitePart v)
        (Nat.pos_iff_ne_zero.mpr hvn) a ha).mpr
      exact (mem_modulusIdeal_iff m (a - 1)).mp h v hv
    · intro v hv
      simpa using hv

theorem modulusIdeal_absNorm (m : RayClassModulus K) :
    Ideal.absNorm (modulusIdeal m) = modulusNorm m := by
  classical
  simp [modulusIdeal, modulusNorm, Finsupp.prod, map_pow, Ideal.absNorm]

theorem modulusNorm_ne_zero (m : RayClassModulus K) : modulusNorm m ≠ 0 := by
  classical
  change ∏ v ∈ m.finitePart.support,
    (Ideal.absNorm v.asIdeal) ^ m.finitePart v ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  apply pow_ne_zero
  intro hzero
  exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp hzero)

theorem modulusIdeal_ne_bot (m : RayClassModulus K) : modulusIdeal m ≠ ⊥ := by
  intro h
  have hnorm := congrArg Ideal.absNorm h
  rw [modulusIdeal_absNorm, Ideal.absNorm_bot] at hnorm
  exact modulusNorm_ne_zero m hnorm

theorem modulusIdeal_eq_top_iff (m : RayClassModulus K) :
    modulusIdeal m = ⊤ ↔ m.finitePart = 0 := by
  constructor
  · intro htop
    by_contra hm0
    obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr hm0
    have honeM : (1 : 𝓞 K) ∈ modulusIdeal m := by simp [htop]
    have hpow := (mem_modulusIdeal_iff m (1 : 𝓞 K)).mp honeM v hv
    have hexp : 1 ≤ m.finitePart v :=
      Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    have hpowle : v.asIdeal ^ m.finitePart v ≤ v.asIdeal :=
      Ideal.pow_le_self (Nat.ne_of_gt hexp)
    have honeP : (1 : 𝓞 K) ∈ v.asIdeal := hpowle hpow
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem v.asIdeal honeP isUnit_one)
  · intro hzero
    simp [modulusIdeal, hzero]

open Classical in
/-- The indicator of the principal ray subgroup, with the exceptional zero value needed for the
trivial finite modulus to make the weight periodic on the one-point quotient by `⊤`. -/
def rayKernelWeight (m : RayClassModulus K) (x : K) : ℝ :=
  if hx : x = 0 then (if m.finitePart = 0 then 1 else 0)
  else if toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx) ∈ rayPrincipalIdealSubgroup m
    then 1 else 0

theorem rayKernelWeight_mem (m : RayClassModulus K) (x : K) :
    rayKernelWeight m x = 0 ∨ rayKernelWeight m x = 1 := by
  classical
  by_cases hx : x = 0
  · by_cases hm : m.finitePart = 0 <;> simp [rayKernelWeight, hx, hm]
  · by_cases h : toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx) ∈ rayPrincipalIdealSubgroup m <;>
      simp [rayKernelWeight, hx, h]

theorem rayKernelWeight_integralUnit (m : RayClassModulus K) (u : (𝓞 K)ˣ) (x : K) :
    rayKernelWeight m (algebraMap (𝓞 K) K (u : 𝓞 K) * x) = rayKernelWeight m x := by
  classical
  by_cases hx : x = 0
  · simp [rayKernelWeight, hx]
  · have hu : algebraMap (𝓞 K) K (u : 𝓞 K) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne (Units.ne_zero u)
    have hux : algebraMap (𝓞 K) K (u : 𝓞 K) * x ≠ 0 := mul_ne_zero hu hx
    have hunit : Units.mk0 (algebraMap (𝓞 K) K (u : 𝓞 K) * x) hux =
        Units.map (algebraMap (𝓞 K) K).toMonoidHom u * Units.mk0 x hx := by
      apply Units.ext
      rfl
    have hprincipal :
        toPrincipalIdeal (𝓞 K) K (Units.mk0 (algebraMap (𝓞 K) K (u : 𝓞 K) * x) hux) =
          toPrincipalIdeal (𝓞 K) K (Units.mk0 x hx) := by
      rw [hunit, toPrincipalIdeal_mul_integralUnit_eq]
    simp only [rayKernelWeight, dif_neg hx, dif_neg hux, hprincipal]

open Classical in
theorem rayKernelWeight_integral_residue [IsTotallyComplex K] (m : RayClassModulus K)
    (a : 𝓞 K) :
    rayKernelWeight m (algebraMap (𝓞 K) K a) =
      if ∃ u : (𝓞 K)ˣ,
        Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
          Ideal.Quotient.mk (modulusIdeal m) a then 1 else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    have hzero :
        (∃ u : (𝓞 K)ˣ,
          Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
            Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K)) ↔ m.finitePart = 0 := by
      constructor
      · rintro ⟨u, hu⟩
        have hu0 : Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) = 0 := by
          simpa using hu
        have huM : (u : 𝓞 K) ∈ modulusIdeal m :=
          Ideal.Quotient.eq_zero_iff_mem.mp hu0
        exact (modulusIdeal_eq_top_iff m).mp
          (Ideal.eq_top_of_isUnit_mem (modulusIdeal m) huM u.isUnit)
      · intro hm
        have htop : modulusIdeal m = ⊤ := (modulusIdeal_eq_top_iff m).mpr hm
        refine ⟨1, ?_⟩
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := modulusIdeal m)
          (1 : 𝓞 K) 0).mpr (by simp [htop])
    by_cases hm : m.finitePart = 0
    · have hP := hzero.mpr hm
      have hP' : ∃ u : (𝓞 K)ˣ,
          Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) = 0 := by simpa using hP
      simp [rayKernelWeight, hm, hP']
    · have hP : ¬ ∃ u : (𝓞 K)ˣ,
          Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
            Ideal.Quotient.mk (modulusIdeal m) (0 : 𝓞 K) :=
        fun hp => hm (hzero.mp hp)
      have hP' : ¬ ∃ u : (𝓞 K)ˣ,
          Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) = 0 := by simpa using hP
      simp [rayKernelWeight, hm, hP']
  · have haK : algebraMap (𝓞 K) K a ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha
    let aK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a) haK
    have hweightOne : rayKernelWeight m (algebraMap (𝓞 K) K a) = 1 ↔
        toPrincipalIdeal (𝓞 K) K aK ∈ rayPrincipalIdealSubgroup m := by
      simp [rayKernelWeight, aK, haK]
    have hcriterion :
        toPrincipalIdeal (𝓞 K) K aK ∈ rayPrincipalIdealSubgroup m ↔
          ∃ u : (𝓞 K)ˣ,
            Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
              Ideal.Quotient.mk (modulusIdeal m) a := by
      constructor
      · intro hprincipal
        obtain ⟨y, hy, hya⟩ :=
          (rayPrincipalIdealSubgroup_mem_iff m
            (toPrincipalIdeal (𝓞 K) K aK)).mp hprincipal
        let z : Kˣ := y * aK⁻¹
        have hz : toPrincipalIdeal (𝓞 K) K z = 1 := by
          dsimp [z]
          rw [map_mul, map_inv, hya]
          simp
        obtain ⟨u, hu⟩ :=
          (RayClass.toPrincipalIdeal_eq_one_iff_mem_integralUnits z).mp hz
        have hyEq : y = RayClass.integralUnitToFieldUnit u * aK := by
          calc
            y = (y * aK⁻¹) * aK := by group
            _ = RayClass.integralUnitToFieldUnit u * aK := by
              rw [hu]
        let b : 𝓞 K := (u : 𝓞 K) * a
        have hb : b ≠ 0 := mul_ne_zero (Units.ne_zero u) ha
        let bK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K b)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hb)
        have hprod : RayClass.integralUnitToFieldUnit u * aK = bK := by
          apply Units.ext
          simp [RayClass.integralUnitToFieldUnit, aK, bK, b]
        have hyb : y = bK := hyEq.trans hprod
        have hrayB : IsRayCongruent m bK := by
          rw [← hyb]
          exact hy
        have hmod : b - 1 ∈ modulusIdeal m :=
          (integral_rayCongruent_iff m b hb).mp hrayB
        let uInv : (𝓞 K)ˣ := u⁻¹
        have hmul : (uInv : 𝓞 K) * (b - 1) ∈ modulusIdeal m :=
          (modulusIdeal m).mul_mem_left (uInv : 𝓞 K) hmod
        have hdiff : (a - (uInv : 𝓞 K)) ∈ modulusIdeal m := by
          have heq : (uInv : 𝓞 K) * (b - 1) = a - (uInv : 𝓞 K) := by
            simp [b, uInv, mul_sub]
          exact heq ▸ hmul
        have hres : Ideal.Quotient.mk (modulusIdeal m) a =
            Ideal.Quotient.mk (modulusIdeal m) (uInv : 𝓞 K) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := modulusIdeal m)
            a (uInv : 𝓞 K)).mpr hdiff
        exact ⟨uInv, hres.symm⟩
      · rintro ⟨u, hres⟩
        have hdiff : a - (u : 𝓞 K) ∈ modulusIdeal m :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := modulusIdeal m)
            a (u : 𝓞 K)).mp hres.symm
        let uInv : (𝓞 K)ˣ := u⁻¹
        let b : 𝓞 K := (uInv : 𝓞 K) * a
        have hb : b ≠ 0 := mul_ne_zero (Units.ne_zero uInv) ha
        let bK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K b)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hb)
        have hmul : (uInv : 𝓞 K) * (a - (u : 𝓞 K)) ∈ modulusIdeal m :=
          (modulusIdeal m).mul_mem_left (uInv : 𝓞 K) hdiff
        have hmod : b - 1 ∈ modulusIdeal m := by
          have heq : (uInv : 𝓞 K) * (a - (u : 𝓞 K)) = b - 1 := by
            simp [b, uInv, mul_sub]
          exact heq ▸ hmul
        have hrayB : IsRayCongruent m bK :=
          (integral_rayCongruent_iff m b hb).mpr hmod
        have hprod : RayClass.integralUnitToFieldUnit uInv * aK = bK := by
          apply Units.ext
          simp [RayClass.integralUnitToFieldUnit, aK, bK, b]
        have hprincipal : toPrincipalIdeal (𝓞 K) K bK =
            toPrincipalIdeal (𝓞 K) K aK := by
          rw [← hprod]
          exact toPrincipalIdeal_mul_integralUnit_eq uInv aK
        exact (rayPrincipalIdealSubgroup_mem_iff m
          (toPrincipalIdeal (𝓞 K) K aK)).mpr ⟨bK, hrayB, hprincipal⟩
    by_cases hres : ∃ u : (𝓞 K)ˣ,
        Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) =
          Ideal.Quotient.mk (modulusIdeal m) a
    · rw [if_pos hres]
      exact hweightOne.mpr (hcriterion.mpr hres)
    · rw [if_neg hres]
      rcases rayKernelWeight_mem m (algebraMap (𝓞 K) K a) with hzero | hone
      · exact hzero
      · exact False.elim (hres (hcriterion.mp (hweightOne.mp hone)))

private theorem not_dvd_heightOne_iff_sup_eq_top
    (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) :
    ¬ v.asIdeal ∣ J ↔ J ⊔ v.asIdeal = ⊤ := by
  constructor
  · intro hnot
    by_contra hsup
    have htopne : v.asIdeal ⊔ J ≠ ⊤ := by
      intro htop
      exact hsup (by simpa [sup_comm] using htop)
    have heq : v.asIdeal = v.asIdeal ⊔ J :=
      v.isMaximal.eq_of_le htopne le_sup_left
    apply hnot
    exact Ideal.dvd_iff_le.mpr (by rw [heq]; exact le_sup_right)
  · intro hsup hdvd
    have hle : J ≤ v.asIdeal := Ideal.dvd_iff_le.mp hdvd
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := by
      calc
        ⊤ = J ⊔ v.asIdeal := hsup.symm
        _ ≤ v.asIdeal := sup_le hle le_rfl
    exact v.isPrime.ne_top (le_antisymm le_top htop)

private theorem integral_count_zero_iff_sup_eq_top
    (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 ↔
      J ⊔ v.asIdeal = ⊤ := by
  have hJ0 : J ≠ (0 : Ideal (𝓞 K)) := by simpa [Ideal.zero_eq_bot] using hJ
  rw [FractionalIdeal.count_coe K v hJ]
  change ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) = 0 ↔ _
  rw [Int.natCast_eq_zero]
  have hcount :
      (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 ↔ v.asIdeal ∣ J := by
    exact Associates.count_ne_zero_iff_dvd hJ0 v.prime.irreducible
  have hzeroNat :
      (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 ↔
        ¬(Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by simp
  rw [hzeroNat, not_congr hcount]
  exact not_dvd_heightOne_iff_sup_eq_top v J

theorem isCoprimeTo_iff_sup (m : RayClassModulus K) (J : Ideal (𝓞 K)) :
    IsCoprimeTo m J ↔ J ≠ ⊥ ∧ J ⊔ modulusIdeal m = ⊤ := by
  constructor
  · rintro ⟨hJ, hprime⟩
    refine ⟨hJ, ?_⟩
    have hprime' : ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count K v
          ((idealUnit J hJ : NumberFieldFractionalIdealGroup K) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := hprime
    have hbase (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
        J ⊔ v.asIdeal = ⊤ := by
      apply (integral_count_zero_iff_sup_eq_top v J hJ).mp
      simpa [idealUnit] using hprime' v hv
    change J ⊔ ∏ v ∈ m.finitePart.support, v.asIdeal ^ m.finitePart v = ⊤
    apply Ideal.sup_prod_eq_top
    intro v hv
    exact Ideal.sup_pow_eq_top' (hbase v hv)
  · rintro ⟨hJ, hsup⟩
    refine ⟨hJ, ?_⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count K v
        ((idealUnit J hJ : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
    intro v hv
    have hvn : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hMle : modulusIdeal m ≤ v.asIdeal ^ m.finitePart v := by
      change (∏ w ∈ m.finitePart.support, w.asIdeal ^ m.finitePart w) ≤ _
      exact (Ideal.prod_le_inf (s := m.finitePart.support)
        (f := fun w => w.asIdeal ^ m.finitePart w)).trans (Finset.inf_le hv)
    have hple : v.asIdeal ^ m.finitePart v ≤ v.asIdeal :=
      Ideal.pow_le_self (Nat.ne_of_gt (Nat.pos_iff_ne_zero.mpr hvn))
    have hbase : J ⊔ v.asIdeal = ⊤ := by
      have htop : (⊤ : Ideal (𝓞 K)) ≤ J ⊔ v.asIdeal := by
        rw [← hsup]
        exact sup_le_sup_left (hMle.trans hple) J
      exact le_antisymm le_top htop
    have hcount := (integral_count_zero_iff_sup_eq_top v J hJ).mpr hbase
    simpa [idealUnit] using hcount

private def rayDenominatorExponent (I : NumberFieldFractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  (NumberFieldFractionalIdealGroup.countVector I).mapRange
    (fun n => max 0 (-n)) (by simp)

private theorem rayDenominatorExponent_nonneg (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ rayDenominatorExponent I v := by
  simp only [rayDenominatorExponent, Finsupp.mapRange_apply]
  exact le_max_left 0 _

private noncomputable irreducible_def rayDenominatorIdeal
    (I : NumberFieldFractionalIdealGroup K) : Ideal (𝓞 K) :=
  (rayDenominatorExponent I).support.prod fun v =>
    v.asIdeal ^ Int.toNat (rayDenominatorExponent I v)

private theorem coe_rayDenominatorIdeal (I : NumberFieldFractionalIdealGroup K) :
    (rayDenominatorIdeal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.factorization
        (Multiplicative.ofAdd (rayDenominatorExponent I)) :
          NumberFieldFractionalIdealGroup K) := by
  classical
  rw [NumberFieldFractionalIdealGroup.factorization_val]
  rw [rayDenominatorIdeal]
  let d := rayDenominatorExponent I
  change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
      (∏ v ∈ d.support, v.asIdeal ^ Int.toNat (d v)) =
    ∏ v ∈ d.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ d v
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro v hv
  have hnat : (Int.toNat (d v) : ℤ) = d v :=
    Int.toNat_of_nonneg (rayDenominatorExponent_nonneg I v)
  rw [← hnat, zpow_natCast]
  rfl

private theorem rayDenominatorIdeal_ne_bot (I : NumberFieldFractionalIdealGroup K) :
    rayDenominatorIdeal I ≠ ⊥ := by
  intro h
  have hcoe :
      (rayDenominatorIdeal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
    rw [h]
    simp
  rw [coe_rayDenominatorIdeal] at hcoe
  exact Units.ne_zero
    (NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd (rayDenominatorExponent I))) hcoe

private theorem rayDenominatorIdeal_count (I : NumberFieldFractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      (rayDenominatorIdeal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        rayDenominatorExponent I v := by
  rw [coe_rayDenominatorIdeal]
  simpa using NumberFieldFractionalIdealGroup.count_factorization
    (Multiplicative.ofAdd (rayDenominatorExponent I)) v

private theorem rayDenominatorIdeal_isCoprimeTo [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    IsCoprimeTo m (rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K)) := by
  let I : NumberFieldFractionalIdealGroup K := A
  let D := rayDenominatorIdeal I
  have hD : D ≠ ⊥ := rayDenominatorIdeal_ne_bot I
  refine ⟨hD, ?_⟩
  change ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      ((idealUnit D hD : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  intro v hv
  have hA : FractionalIdeal.count K v
      ((A : NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := A.2 v hv
  have hDcount := rayDenominatorIdeal_count I v
  have hcountI : NumberFieldFractionalIdealGroup.countVector I v = 0 := by
    simpa [I] using hA
  have hzero : rayDenominatorExponent I v = 0 := by
    simp [rayDenominatorExponent, hcountI]
  simpa [D, idealUnit, hDcount, hzero]

set_option maxHeartbeats 1000000 in
private theorem rayDenominatorIdeal_comaximal [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ⊔ modulusIdeal m = ⊤ := by
  exact ((isCoprimeTo_iff_sup m (rayDenominatorIdeal
    (A : NumberFieldFractionalIdealGroup K))).mp
      (rayDenominatorIdeal_isCoprimeTo m A)).2

set_option maxHeartbeats 1000000 in
private theorem exists_crt_nonzero_element (D M : Ideal (𝓞 K))
    (hDM : D ⊔ M = ⊤) (hM : M ≠ ⊤) :
    ∃ d : 𝓞 K, d ∈ D ∧ d ≠ 0 ∧ d - 1 ∈ M := by
  obtain ⟨d, hd, e, he, hde⟩ := (Ideal.isCoprime_iff_sup_eq.mpr hDM).exists
  have hdz : d ≠ 0 := by
    intro h0
    have hmem : d + e ∈ M := by simpa [h0] using he
    have hone : (1 : 𝓞 K) ∈ M := by simpa [hde] using hmem
    exact hM (Ideal.eq_top_of_isUnit_mem M hone isUnit_one)
  have hmod : d - 1 ∈ M := by
    have hneg : d - 1 = -e := by
      calc
        d - 1 = d - (d + e) := by rw [← hde]
        _ = -e := by ring
    rw [hneg]
    exact M.neg_mem he
  exact ⟨d, hd, hdz, hmod⟩

set_option maxHeartbeats 1000000 in
private theorem exists_rayDenominator_of_modulus_top
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m)
    (htop : modulusIdeal m = ⊤) :
    ∃ d : 𝓞 K, d ≠ 0 ∧
      d ∈ rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ∧
      d - 1 ∈ modulusIdeal m := by
  let D := rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K)
  have hD : D ≠ ⊥ := by
    change rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ≠ ⊥
    exact rayDenominatorIdeal_ne_bot (A : NumberFieldFractionalIdealGroup K)
  obtain ⟨d, hd, hdz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  exact ⟨d, hdz, hd, by simp [htop]⟩

set_option maxHeartbeats 20000000 in
private theorem exists_rayDenominator_of_modulus_ne_top [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m)
    (htop : modulusIdeal m ≠ ⊤) :
    ∃ d : 𝓞 K, d ≠ 0 ∧
      d ∈ rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ∧
      d - 1 ∈ modulusIdeal m := by
  let D := rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K)
  have hD : D ≠ ⊥ := by
    change rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ≠ ⊥
    exact rayDenominatorIdeal_ne_bot (A : NumberFieldFractionalIdealGroup K)
  have hDM : D ⊔ modulusIdeal m = ⊤ := rayDenominatorIdeal_comaximal m A
  obtain ⟨d, hd, hdz, hmod⟩ := exists_crt_nonzero_element D (modulusIdeal m) hDM htop
  exact ⟨d, hdz, hd, hmod⟩

private theorem exists_rayCongruent_denominator [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    ∃ d : 𝓞 K, d ≠ 0 ∧
      d ∈ rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K) ∧
      d - 1 ∈ modulusIdeal m := by
  classical
  by_cases htop : modulusIdeal m = ⊤
  · exact exists_rayDenominator_of_modulus_top m A htop
  · exact exists_rayDenominator_of_modulus_ne_top m A htop

private theorem modulusIdeal_le_primePower (m : RayClassModulus K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
    modulusIdeal m ≤ v.asIdeal ^ m.finitePart v := by
  change (∏ w ∈ m.finitePart.support, w.asIdeal ^ m.finitePart w) ≤ _
  exact (Ideal.prod_le_inf (s := m.finitePart.support)
    (f := fun w => w.asIdeal ^ m.finitePart w)).trans (Finset.inf_le hv)

private theorem count_toPrincipalIdeal_integral (v : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ≠ 0) :
    FractionalIdeal.count K v
      (toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
  rfl

private theorem rayCongruent_integralPrincipal_primeTo (m : RayClassModulus K)
    (a : 𝓞 K) (ha : a ≠ 0) (hmod : a - 1 ∈ modulusIdeal m) :
    toPrincipalIdeal (𝓞 K) K
      (Units.mk0 (algebraMap (𝓞 K) K a)
        ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) ∈
      rayClassPrimeToIdeals m := by
  change ∀ v, v ∈ m.finitePart.support →
    FractionalIdeal.count K v
      (toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
  intro v hv
  have hpow : a - 1 ∈ v.asIdeal ^ m.finitePart v :=
    modulusIdeal_le_primePower m v hv hmod
  have hpos : 1 ≤ m.finitePart v :=
    Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  have hmodv : a - 1 ∈ v.asIdeal :=
    (Ideal.pow_le_self (Nat.ne_of_gt hpos)) hpow
  have haNot : a ∉ v.asIdeal := by
    intro haP
    have hone : (1 : 𝓞 K) ∈ v.asIdeal := by
      simpa [sub_sub] using sub_mem haP hmodv
    exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem v.asIdeal hone isUnit_one)
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp ha
  have hspan : Ideal.span {a} ⊔ v.asIdeal = ⊤ := by
    apply (not_dvd_heightOne_iff_sup_eq_top v (Ideal.span {a})).mp
    intro hdvd
    exact haNot ((Ideal.dvd_iff_le.mp hdvd) (Ideal.subset_span rfl))
  have hcount : FractionalIdeal.count K v
      (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 :=
    (integral_count_zero_iff_sup_eq_top v (Ideal.span {a}) hspan0).mpr hspan
  rw [count_toPrincipalIdeal_integral v a ha]
  exact hcount

private theorem denominator_count_le_integralPrincipal_count
    (I : NumberFieldFractionalIdealGroup K) (a : 𝓞 K) (ha : a ≠ 0)
    (haD : a ∈ rayDenominatorIdeal I) (v : HeightOneSpectrum (𝓞 K)) :
    rayDenominatorExponent I v ≤
      FractionalIdeal.count K v
        (toPrincipalIdeal (𝓞 K) K
          (Units.mk0 (algebraMap (𝓞 K) K a)
            ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp ha
  have hspanLe : (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      (rayDenominatorIdeal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    apply (FractionalIdeal.coeIdeal_le_coeIdeal K).2
    exact (Ideal.span_singleton_le_iff_mem (rayDenominatorIdeal I)).mpr haD
  have hmono := FractionalIdeal.count_mono K v
    (FractionalIdeal.coeIdeal_ne_zero.mpr hspan0) hspanLe
  have hmono' :
      rayDenominatorExponent I v ≤
        FractionalIdeal.count K v
          (toPrincipalIdeal (𝓞 K) K
            (Units.mk0 (algebraMap (𝓞 K) K a)
              ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    calc
      rayDenominatorExponent I v =
          FractionalIdeal.count K v
            (rayDenominatorIdeal I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        (rayDenominatorIdeal_count I v).symm
      _ ≤ FractionalIdeal.count K v
          (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := hmono
      _ = FractionalIdeal.count K v
          (toPrincipalIdeal (𝓞 K) K
            (Units.mk0 (algebraMap (𝓞 K) K a)
              ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        (count_toPrincipalIdeal_integral v a ha).symm
  exact hmono'

private def integralIdealOfExponent (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, 0 ≤ e v) : Ideal (𝓞 K) :=
  e.support.prod fun v => v.asIdeal ^ Int.toNat (e v)

private theorem coe_integralIdealOfExponent (e : HeightOneSpectrum (𝓞 K) →₀ ℤ)
    (he : ∀ v, 0 ≤ e v) :
    (integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) :
        NumberFieldFractionalIdealGroup K) := by
  classical
  rw [NumberFieldFractionalIdealGroup.factorization_val]
  change (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
      (∏ v ∈ e.support, v.asIdeal ^ Int.toNat (e v)) =
    ∏ v ∈ e.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ e v
  rw [map_prod]
  simp only [map_pow]
  apply Finset.prod_congr rfl
  intro v hv
  have hnat : (Int.toNat (e v) : ℤ) = e v := Int.toNat_of_nonneg (he v)
  rw [← hnat, zpow_natCast]
  rfl

private theorem factorization_countVector (I : NumberFieldFractionalIdealGroup K) :
    NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd (NumberFieldFractionalIdealGroup.countVector I)) = I := by
  apply NumberFieldFractionalIdealGroup.ext_count
  intro v
  rw [NumberFieldFractionalIdealGroup.count_factorization]
  exact NumberFieldFractionalIdealGroup.countVector_apply I v

private theorem fractional_le_one_of_count_nonneg (I : NumberFieldFractionalIdealGroup K)
    (hI : ∀ v, 0 ≤ FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 := by
  let e := NumberFieldFractionalIdealGroup.countVector I
  have he : ∀ v, 0 ≤ e v := by
    intro v
    simpa [e] using hI v
  have hcoe :
      (integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    calc
      (integralIdealOfExponent e he : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) :
            NumberFieldFractionalIdealGroup K) := coe_integralIdealOfExponent e he
      _ = (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
        congrArg Units.val (by simpa [e] using factorization_countVector I)
  rw [← hcoe]
  exact FractionalIdeal.coeIdeal_le_one

private theorem exists_integral_ideal_of_principal_mul_rayIdeal [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m)
    (a : 𝓞 K) (ha : a ≠ 0)
    (haD : a ∈ rayDenominatorIdeal (A : NumberFieldFractionalIdealGroup K))
    (hmod : a - 1 ∈ modulusIdeal m) :
    ∃ J : Ideal (𝓞 K), ∃ hJ : IsCoprimeTo m J,
      idealUnit J hJ.1 =
        toPrincipalIdeal (𝓞 K) K
          (Units.mk0 (algebraMap (𝓞 K) K a)
            ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)) *
          (A : NumberFieldFractionalIdealGroup K) := by
  let aK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K a)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne ha)
  let P : NumberFieldFractionalIdealGroup K := toPrincipalIdeal (𝓞 K) K aK
  let F : NumberFieldFractionalIdealGroup K := P * (A : NumberFieldFractionalIdealGroup K)
  have hPprime : P ∈ rayClassPrimeToIdeals m := by
    simpa [P, aK] using rayCongruent_integralPrincipal_primeTo m a ha hmod
  have hFprime : F ∈ rayClassPrimeToIdeals m :=
    (rayClassPrimeToIdeals m).mul_mem hPprime A.2
  have hFcountNonneg : ∀ v : HeightOneSpectrum (𝓞 K),
      0 ≤ FractionalIdeal.count K v (F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro v
    have hpc : rayDenominatorExponent (A : NumberFieldFractionalIdealGroup K) v ≤
        FractionalIdeal.count K v
        (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
      denominator_count_le_integralPrincipal_count
        (A : NumberFieldFractionalIdealGroup K) a ha haD v
    have hA : FractionalIdeal.count K v
        ((A : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        NumberFieldFractionalIdealGroup.countVector A v := by
      exact (NumberFieldFractionalIdealGroup.countVector_apply A v).symm
    have hbase : 0 ≤ rayDenominatorExponent (A : NumberFieldFractionalIdealGroup K) v +
        NumberFieldFractionalIdealGroup.countVector A v := by
      simp only [rayDenominatorExponent, Finsupp.mapRange_apply]
      omega
    have hmul := FractionalIdeal.count_mul K v (Units.ne_zero P) (Units.ne_zero A)
    calc
      0 ≤ rayDenominatorExponent (A : NumberFieldFractionalIdealGroup K) v +
          NumberFieldFractionalIdealGroup.countVector A v := hbase
      _ ≤ FractionalIdeal.count K v (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) +
          FractionalIdeal.count K v
            ((A : NumberFieldFractionalIdealGroup K) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
            rw [← hA]
            simpa [add_comm] using
              add_le_add_left hpc (NumberFieldFractionalIdealGroup.countVector A v)
      _ = FractionalIdeal.count K v (F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
            simpa [F] using hmul.symm
  have hFle : (F : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 :=
    fractional_le_one_of_count_nonneg F hFcountNonneg
  obtain ⟨J, hJcoe⟩ :=
    (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hFle
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hzero : (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 := by
      simp [hbot]
    rw [hJcoe] at hzero
    exact Units.ne_zero F hzero
  have hunitJ : idealUnit J hJ = F := by
    apply Units.ext
    exact hJcoe
  have hcop : IsCoprimeTo m J := ⟨hJ, by rw [hunitJ]; exact hFprime⟩
  exact ⟨J, hcop, hunitJ⟩

private theorem exists_integral_rayClass_ideal [IsTotallyComplex K]
    (m : RayClassModulus K) (A : rayClassPrimeToIdeals m) :
    ∃ J : Ideal (𝓞 K), ∃ hJ : IsCoprimeTo m J,
      rayClass m J hJ =
        QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) A := by
  obtain ⟨d, hd, hdD, hmod⟩ := exists_rayCongruent_denominator m A
  obtain ⟨J, hJ, hunitJ⟩ :=
    exists_integral_ideal_of_principal_mul_rayIdeal m A d hd hdD hmod
  let dK : Kˣ := Units.mk0 (algebraMap (𝓞 K) K d)
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd)
  have hdRay : IsRayCongruent m dK :=
    (integral_rayCongruent_iff m d hd).mpr hmod
  have hPprime := rayCongruent_integralPrincipal_primeTo m d hd hmod
  let pD : rayClassPrimeToIdeals m := ⟨toPrincipalIdeal (𝓞 K) K dK, hPprime⟩
  have hpMem : pD ∈ rayPrincipalIdealSubgroupInPrimeTo m :=
    (rayPrincipalIdealSubgroupInPrimeTo_mem_iff m pD).mpr ⟨dK, hdRay, rfl⟩
  have hpq : QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) pD = 1 :=
    (QuotientGroup.eq_one_iff (N := rayPrincipalIdealSubgroupInPrimeTo m) pD).mpr hpMem
  have hsubprod : (⟨idealUnit J hJ.1, hJ.2⟩ : rayClassPrimeToIdeals m) = pD * A := by
    apply Subtype.ext
    change idealUnit J hJ.1 =
      toPrincipalIdeal (𝓞 K) K dK * (A : NumberFieldFractionalIdealGroup K)
    simpa [dK] using hunitJ
  have hclass : rayClass m J hJ =
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) A := by
    change QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)
      (⟨idealUnit J hJ.1, hJ.2⟩ : rayClassPrimeToIdeals m) = _
    rw [hsubprod]
    calc
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) (pD * A) =
      QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) pD *
            QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) A := by simp
      _ = QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) A := by
        rw [hpq]
        exact one_mul (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m) A)
  exact ⟨J, hJ, hclass⟩

theorem exists_integralRayRepresentatives [IsTotallyComplex K]
    (m : RayClassModulus K) : Nonempty (IntegralRayRepresentatives m) := by
  classical
  let N := rayPrincipalIdealSubgroupInPrimeTo m
  let A : RayClassGroup m → rayClassPrimeToIdeals m := fun C =>
    Classical.choose (QuotientGroup.mk'_surjective N (C⁻¹))
  have hA (C : RayClassGroup m) : QuotientGroup.mk' N (A C) = C⁻¹ :=
    Classical.choose_spec (QuotientGroup.mk'_surjective N (C⁻¹))
  let J : RayClassGroup m → Ideal (𝓞 K) := fun C =>
    Classical.choose (exists_integral_rayClass_ideal m (A C))
  let hJ (C : RayClassGroup m) : IsCoprimeTo m (J C) :=
    Classical.choose (Classical.choose_spec (exists_integral_rayClass_ideal m (A C)))
  have hClass (C : RayClassGroup m) : rayClass m (J C) (hJ C) =
      QuotientGroup.mk' N (A C) :=
    Classical.choose_spec (Classical.choose_spec (exists_integral_rayClass_ideal m (A C)))
  have hClass' (C : RayClassGroup m) : rayClass m (J C) (hJ C) = C⁻¹ := by
    rw [hClass C, hA C]
  exact ⟨⟨J, hJ, hClass'⟩⟩

local instance finiteModulusQuotient (m : RayClassModulus K) :
    Finite ((𝓞 K) ⧸ modulusIdeal m) := by
  letI : NeZero (modulusIdeal m) := ⟨modulusIdeal_ne_bot m⟩
  infer_instance

/-- Residue classes modulo the finite modulus that are represented by integral units. -/
def acceptedResidues (m : RayClassModulus K) :=
  {r : (𝓞 K) ⧸ modulusIdeal m //
    ∃ u : (𝓞 K)ˣ, Ideal.Quotient.mk (modulusIdeal m) (u : 𝓞 K) = r}

local instance finiteAcceptedResidues (m : RayClassModulus K) : Finite (acceptedResidues m) :=
  Finite.of_injective (fun r : acceptedResidues m => r.1) Subtype.val_injective

/-- The common number of residue cosets selected by the ray kernel weight. -/
def residueCount (m : RayClassModulus K) : ℕ := Nat.card (acceptedResidues m)

theorem residueCount_pos (m : RayClassModulus K) : 0 < residueCount m := by
  have hne : Nonempty (acceptedResidues m) := by
    refine ⟨⟨Ideal.Quotient.mk (modulusIdeal m) (1 : 𝓞 K), ?_⟩⟩
    exact ⟨1, rfl⟩
  exact Nat.card_pos

theorem integral_residue_surjective_of_sup_eq (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hJM : J ⊔ modulusIdeal m = ⊤) :
    Function.Surjective (fun x : J => Ideal.Quotient.mk (modulusIdeal m) x.1) := by
  intro r
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := modulusIdeal m) r
  have hcop : IsCoprime J (modulusIdeal m) := Ideal.isCoprime_iff_sup_eq.mpr hJM
  obtain ⟨i, hi, j, hj, hij⟩ := hcop.exists
  have hxi : x * i ∈ J := J.mul_mem_left x hi
  have hxj : x * j ∈ modulusIdeal m := (modulusIdeal m).mul_mem_left x hj
  have hdecomp : x = x * i + x * j := by
    calc
      x = x * 1 := by simp
      _ = x * (i + j) := by rw [hij]
      _ = x * i + x * j := mul_add x i j
  have hmk : Ideal.Quotient.mk (modulusIdeal m) x =
      Ideal.Quotient.mk (modulusIdeal m) (x * i) := by
    calc
      Ideal.Quotient.mk (modulusIdeal m) x =
          Ideal.Quotient.mk (modulusIdeal m) (x * i + x * j) := by rw [← hdecomp]
      _ = Ideal.Quotient.mk (modulusIdeal m) (x * i) +
          Ideal.Quotient.mk (modulusIdeal m) (x * j) := by rw [map_add]
      _ = Ideal.Quotient.mk (modulusIdeal m) (x * i) := by
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hxj, add_zero]
  refine ⟨⟨x * i, hxi⟩, ?_⟩
  exact hmk.symm.trans hx

theorem integral_residue_kernel_of_sup_eq (m : RayClassModulus K)
    (J : Ideal (𝓞 K)) (hJM : J ⊔ modulusIdeal m = ⊤) (x : J) :
    Ideal.Quotient.mk (modulusIdeal m) x.1 = 0 ↔
      x.1 ∈ modulusIdeal m * J := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hcop : IsCoprime (modulusIdeal m) J :=
    Ideal.isCoprime_iff_sup_eq.mpr (by simpa [sup_comm] using hJM)
  constructor
  · intro hx
    rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact ⟨hx, x.2⟩
  · intro hx
    rw [Ideal.mul_eq_inf_of_isCoprime hcop] at hx
    exact hx.1

end ArtinPrimitiveRoots.Hecke

end
