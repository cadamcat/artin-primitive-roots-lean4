import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.RayClassCopy

/-!
# Local form of the copied ray congruence

This is a local lemma for the copied `ClassFieldTheory` ray-class interface. Its reduction step
follows the construction of `ClassFieldTheory.rayLocalHigherUnitMap` (ClassFieldTheory, Apache-2.0).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

variable {F : Type} [Field F] [NumberField F]

theorem localUnit_mem_rayLocalHigherUnitGroup_of_congruent
    (v : FinPlace F) (n : ℕ) (a : 𝓞 F) (x : Fˣ)
    (hx : (x : F) = algebraMap (𝓞 F) F a) (ha : a ∉ v.asIdeal)
    (hcong : a - 1 ∈ v.asIdeal ^ n) :
    finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v n := by
  classical
  let u := finitePlaceUnitEmbedding v x
  have huval : Valued.v (u : v.adicCompletion F) = 1 := by
    calc
      Valued.v (u : v.adicCompletion F) =
          Valued.v (algebraMap (𝓞 F) F a : v.adicCompletion F) := by
        change Valued.v ((x : F) : v.adicCompletion F) = _
        rw [hx]
      _ = v.valuation F (algebraMap (𝓞 F) F a) :=
        v.valuedAdicCompletion_eq_valuation a
      _ = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 ha
  have huInt : u ∈ (v.adicCompletionIntegers F).units :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (K := F) (v := v)).2 huval
  let y : (v.adicCompletionIntegers F).units := ⟨u, huInt⟩
  let vC : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have hEquiv : vC.IsEquiv (v.adicCompletionIntegers F).valuation :=
    Valuation.isEquiv_valuation_valuationSubring vC
  have hmapPrime : Ideal.map
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) v.asIdeal ≤
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have hval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) b) < 1 := by
      have hvalEq : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) b) =
          v.valuation F (algebraMap (𝓞 F) F b) := by
        have hmap : algebraMap (𝓞 F) (v.adicCompletion F) b =
            (algebraMap (𝓞 F) F b : v.adicCompletion F) :=
          congrFun (HeightOneSpectrum.algebraMap_adicCompletion
            (S := 𝓞 F) (K := F) (v := v)) b
        rw [hmap]
        exact v.valuedAdicCompletion_eq_valuation b
      exact hvalEq.trans_lt ((v.valuation_lt_one_iff_mem (K := F) b).2 hb)
    change algebraMap (𝓞 F) (v.adicCompletionIntegers F) b ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
    have hvalS : (v.adicCompletionIntegers F).valuation
        (algebraMap (𝓞 F) (v.adicCompletion F) b) < 1 :=
      (Valuation.isEquiv_iff_val_lt_one.mp hEquiv).mp hval
    have hnon : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) b :
        v.adicCompletion F) ∈ (v.adicCompletionIntegers F).nonunits := by
      rw [ValuationSubring.mem_nonunits_iff]
      exact hvalS
    exact (ValuationSubring.coe_mem_nonunits_iff).1 hnon
  have hmapPow : Ideal.map
      (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) (v.asIdeal ^ n) ≤
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmapPrime n
  have hlocal :
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - 1) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n :=
    hmapPow (Ideal.mem_map_of_mem _ hcong)
  have hy : (((v.adicCompletionIntegers F).unitsEquivUnitsType y :
      (v.adicCompletionIntegers F).toSubmonoidˣ).1 : v.adicCompletionIntegers F) =
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) a := by
    apply Subtype.ext
    change (u : v.adicCompletion F) = _
    change algebraMap F (v.adicCompletion F) (x : F) = _
    rw [hx]
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply
      (R := 𝓞 F) (K := F) v a]
    change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) =
      (algebraMap (𝓞 F) F a : v.adicCompletion F)
    rfl
  have hdiff : algebraMap (𝓞 F) (v.adicCompletionIntegers F) a - 1 =
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) (a - 1) := by simp
  have hker : rayLocalHigherUnitMap v n y = 1 := by
    change Units.map
        (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n)).toMonoidHom
        ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y) = 1
    apply Units.ext
    change Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ n)
        (((v.adicCompletionIntegers F).unitsEquivUnitsType y :
          (v.adicCompletionIntegers F).toSubmonoidˣ).1 : v.adicCompletionIntegers F) = 1
    rw [Ideal.Quotient.mk_eq_one_iff_sub_mem, hy, hdiff]
    exact hlocal
  rw [rayLocalHigherUnitGroup, Subgroup.mem_map]
  refine ⟨y, hker, ?_⟩
  change (v.adicCompletionIntegers F).units.subtype y = finitePlaceUnitEmbedding v x
  rfl

end ArtinPrimitiveRoots.Dictionary
