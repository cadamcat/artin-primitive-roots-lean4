import Mathlib
import ArtinPrimitiveRoots.A1.Characters
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.hk_misc_p

private noncomputable def d1CompletionIntegerUniformizer
    {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletionIntegers K :=
  ⟨algebraMap K (v.adicCompletion K) (ArtinPrimitiveRoots.A1.unif (F := K) v), by
    change Valued.v (algebraMap K (v.adicCompletion K)
      (ArtinPrimitiveRoots.A1.unif (F := K) v)) ≤ 1
    have hmap : algebraMap K (v.adicCompletion K)
        (ArtinPrimitiveRoots.A1.unif (F := K) v) =
        (ArtinPrimitiveRoots.A1.unif (F := K) v : v.adicCompletion K) := by
      simpa using congrFun
        (HeightOneSpectrum.algebraMap_adicCompletion (S := K) (K := K) (v := v))
        (ArtinPrimitiveRoots.A1.unif (F := K) v)
    have hval := v.valuedAdicCompletion_eq_valuation'
      (ArtinPrimitiveRoots.A1.unif (F := K) v)
    have hunif : v.valuation K (ArtinPrimitiveRoots.A1.unif (F := K) v) =
        WithZero.exp (-1 : ℤ) := by
      simpa [ArtinPrimitiveRoots.A1.unif] using
        (HeightOneSpectrum.valuation_exists_uniformizer K v).choose_spec
    rw [hmap, hval, hunif]
    exact (WithZero.exp_le_one_iff).mpr (by norm_num)⟩

private theorem d1CompletionIntegerUniformizer_val
    {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (d1CompletionIntegerUniformizer v : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
  change Valued.v (algebraMap K (v.adicCompletion K)
    (ArtinPrimitiveRoots.A1.unif (F := K) v)) = _
  have hmap : algebraMap K (v.adicCompletion K)
      (ArtinPrimitiveRoots.A1.unif (F := K) v) =
      (ArtinPrimitiveRoots.A1.unif (F := K) v : v.adicCompletion K) := by
    simpa using congrFun
      (HeightOneSpectrum.algebraMap_adicCompletion (S := K) (K := K) (v := v))
      (ArtinPrimitiveRoots.A1.unif (F := K) v)
  rw [hmap, v.valuedAdicCompletion_eq_valuation'
    (ArtinPrimitiveRoots.A1.unif (F := K) v)]
  simpa [ArtinPrimitiveRoots.A1.unif] using
    (HeightOneSpectrum.valuation_exists_uniformizer K v).choose_spec

/-- Local higher-unit membership is exactly integrality of the unit and its inverse together with
the normalized valuation bound on `u - 1`. -/
theorem d1_mem_rayLocalHigherUnitGroup_iff
    {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (u : (v.adicCompletion K)ˣ) :
    u ∈ rayLocalHigherUnitGroup v n ↔
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
        v.adicCompletionIntegers K ∧
      Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  let A : ValuationSubring (v.adicCompletion K) := v.adicCompletionIntegers K
  let J := IsLocalRing.maximalIdeal A
  let π : A := d1CompletionIntegerUniformizer v
  let vC : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  have hInt : vC.Integers A := by
    change vC.Integers vC.valuationSubring
    exact Valuation.valuationSubring.integers vC
  have hπval : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    simpa [π] using d1CompletionIntegerUniformizer_val v
  have hmax : J = Ideal.span {π} := by
    have hmaxSet : (J : Set A) = {x : A | Valued.v (x : v.adicCompletion K) < 1} := by
      ext x
      change x ∈ IsLocalRing.maximalIdeal A ↔ vC (x : v.adicCompletion K) < 1
      exact Valuation.mem_maximalIdeal_iff (v := vC)
    have hspanSet : (Ideal.span {π} : Set A) =
        {x : A | Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ)} := by
      simpa [vC, hπval, ValuationSubring.algebraMap_apply] using
        hInt.coe_span_singleton_eq_setOfPred_le_v_algebraMap π
    have hsets : {x : A | Valued.v (x : v.adicCompletion K) < 1} =
        {x : A | Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ)} := by
      ext x
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hvx : Valued.v (x : v.adicCompletion K) ≠ 0 := by
            intro hz
            exact hx0 (Subtype.ext ((Valuation.zero_iff Valued.v).mp hz))
          have hxlt : Valued.v (x : v.adicCompletion K) < 1 := by
            simpa only [Set.mem_setOf_eq] using hx
          have hlog : WithZero.log (Valued.v (x : v.adicCompletion K)) < 0 := by
            apply WithZero.exp_lt_one_iff.mp
            simpa only [WithZero.exp_log hvx] using hxlt
          have hlog' : WithZero.log (Valued.v (x : v.adicCompletion K)) ≤ -1 := by omega
          calc
            Valued.v (x : v.adicCompletion K) =
                WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion K))) :=
                  (WithZero.exp_log hvx).symm
            _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr hlog'
      · intro hx
        exact hx.trans_lt (WithZero.exp_lt_one_iff.mpr (by norm_num))
    exact SetLike.coe_injective (hmaxSet.trans (hsets.trans hspanSet.symm))
  have hπirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hmax
  have hpowSet (k : ℕ) : ((J ^ k : Ideal A) : Set A) =
      {x : A | Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-(k : ℤ))} := by
    rw [hInt.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hπirr k]
    have hpv : (Valued.v (algebraMap A (v.adicCompletion K) π)) ^ k =
        WithZero.exp (-(k : ℤ)) := by
      simpa [ValuationSubring.algebraMap_apply] using (by
        rw [hπval]
        simpa using (WithZero.exp_zsmul (k : ℤ) (-1 : ℤ)).symm :
          (Valued.v (π : v.adicCompletion K)) ^ k = WithZero.exp (-(k : ℤ)))
    rw [hpv]
    ext x
    simp [ValuationSubring.algebraMap_apply, vC]
  constructor
  · intro hu
    rw [rayLocalHigherUnitGroup, Subgroup.mem_map] at hu
    rcases hu with ⟨y, hyker, hy⟩
    let z : A.toSubmonoidˣ := A.toSubmonoid.unitsEquivUnitsType y
    let zval : A := ⟨(z.val : v.adicCompletion K), z.val.property⟩
    have hquot : Ideal.Quotient.mk (J ^ n) zval = 1 := by
      have h := hyker
      change Units.map (Ideal.Quotient.mk (J ^ n)).toMonoidHom
        (A.toSubmonoid.unitsEquivUnitsType y) = 1 at h
      have hval := congrArg Units.val h
      change Ideal.Quotient.mk (J ^ n) zval = 1 at hval
      exact hval
    have hcong : zval - (1 : A) ∈ (J ^ n : Ideal A) :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := J ^ n) zval).mp hquot
    have hyval : (zval : v.adicCompletion K) = (u : v.adicCompletion K) := by
      have h := congrArg Units.val hy
      change (zval : v.adicCompletion K) = (u : v.adicCompletion K) at h
      exact h
    let zInv : A.toSubmonoidˣ := A.toSubmonoid.unitsEquivUnitsType y⁻¹
    let zInvval : A := ⟨(zInv.val : v.adicCompletion K), zInv.val.property⟩
    have hboundA : Valued.v ((zval - (1 : A) : A) : v.adicCompletion K) ≤
        WithZero.exp (-(n : ℤ)) := by
      have hmem : zval - (1 : A) ∈ ((J ^ n : Ideal A) : Set A) := hcong
      rw [hpowSet n] at hmem
      exact hmem
    refine ⟨?_, ?_, ?_⟩
    · rw [← hyval]
      exact zval.property
    · rw [show ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          (zInvval : v.adicCompletion K) by
        have hyInv : A.units.subtype y⁻¹ = u⁻¹ := by rw [map_inv, hy]
        have h := congrArg Units.val hyInv
        change ((zInv : A.toSubmonoidˣ).val : v.adicCompletion K) =
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) at h
        calc
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
              ((zInv : A.toSubmonoidˣ).val : v.adicCompletion K) := h.symm
          _ = (zInvval : v.adicCompletion K) := rfl]
      exact zInvval.property
    · rw [← hyval]
      simpa using hboundA
  · rintro ⟨hu, huinv, hbound⟩
    let zval : A := ⟨(u : v.adicCompletion K), hu⟩
    have huVal : Valued.v (u : v.adicCompletion K) ≤ 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hu
    have huinvVal : Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1 := by
      simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using huinv
    have hinvVal : (Valued.v (u : v.adicCompletion K))⁻¹ ≤ 1 := by
      simpa [Units.val_inv_eq_inv_val, map_inv₀] using huinvVal
    have hpos : 0 < Valued.v (u : v.adicCompletion K) :=
      (Valuation.pos_iff Valued.v).2 u.ne_zero
    have hval : Valued.v (u : v.adicCompletion K) = 1 :=
      le_antisymm huVal ((inv_le_one₀ hpos).mp hinvVal)
    have hyunit : u ∈ A.units :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (K := K) (v := v)).2 hval
    let y : A.units := ⟨u, hyunit⟩
    have hmemPow : zval - (1 : A) ∈ ((J ^ n : Ideal A) : Set A) := by
      change zval - (1 : A) ∈ ((J ^ n : Ideal A) : Set A)
      rw [hpowSet n]
      change Valued.v ((u : v.adicCompletion K) - 1) ≤ _
      exact hbound
    have hquot : Ideal.Quotient.mk (J ^ n) zval = 1 :=
      (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := J ^ n) zval).mpr hmemPow
    have hker : rayLocalHigherUnitMap v n y = 1 := by
      change Units.map (Ideal.Quotient.mk (J ^ n)).toMonoidHom
        (A.toSubmonoid.unitsEquivUnitsType y) = 1
      apply Units.ext
      change Ideal.Quotient.mk (J ^ n) zval = 1
      exact hquot
    rw [rayLocalHigherUnitGroup, Subgroup.mem_map]
    refine ⟨y, hker, ?_⟩
    apply Units.ext
    change (u : v.adicCompletion K) = (u : v.adicCompletion K)
    rfl

end ArtinPrimitiveRoots.Proofs.hk_misc_p
