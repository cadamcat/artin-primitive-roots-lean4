import ArtinPrimitiveRoots.A1.Residue
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Residue and local-unit conditions

The next bridge, in this module's context, is:
```
theorem qs_nq0_residue_ne_zero_iff_valuation_one (v : FinPlace K) (x : K) :
    residue v x ≠ 0 ↔ v.valuation K x = 1

theorem qs_nq0_count_spanSingleton_eq_neg_log_valuation (v : FinPlace K)
    (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) =
      -WithZero.log (v.valuation K x)
```
-/

set_option autoImplicit false

open scoped NumberField
open ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- Nonzero residue is exactly the global valuation-one condition. -/
theorem qs_nq0_residue_ne_zero_iff_valuation_one (v : FinPlace K) (x : K) :
    residue v x ≠ 0 ↔ v.valuation K x = 1 := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  unfold residue
  split_ifs with h
  · have hdv : v.valuation K (algebraMap (𝓞 K) K h.choose.2) = 1 :=
      v.valuation_eq_one_iff_notMem.mpr h.choose_spec.1
    have hdq : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 :=
      (not_congr Ideal.Quotient.eq_zero_iff_mem).mpr h.choose_spec.1
    have hv := congrArg (v.valuation K) h.choose_spec.2
    rw [map_mul, hdv, mul_one] at hv
    rw [mul_ne_zero_iff, hv, v.valuation_eq_one_iff_notMem]
    constructor
    · intro hx
      exact (not_congr Ideal.Quotient.eq_zero_iff_mem).mp hx.1
    · intro hx
      exact ⟨(not_congr Ideal.Quotient.eq_zero_iff_mem).mpr hx, inv_ne_zero hdq⟩
  · constructor
    · intro hx
      exact (hx rfl).elim
    · intro hx
      obtain ⟨n, d, hnd⟩ :=
        v.exists_primeCompl_mul_eq_of_integer x (le_of_eq hx)
      exact (h ⟨(n, (d : 𝓞 K)), d.property, hnd⟩).elim

/-- The prime exponent of a principal fractional ideal is the valuation logarithm. -/
theorem qs_nq0_count_spanSingleton_eq_neg_log_valuation (v : FinPlace K)
    (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x) =
      -WithZero.log (v.valuation K x) := by
  have hdiv (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a / b)) =
        FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a) -
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b) := by
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
      FractionalIdeal.count_mul K v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
        (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb)),
      FractionalIdeal.count_inv]
    ring
  have hint (r : 𝓞 K) (hr : r ≠ 0) :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (algebraMap (𝓞 K) K r)) =
        -WithZero.log (v.intValuation r) := by
    have hspan : (Ideal.span {r} : Ideal (𝓞 K)) ≠ 0 := by
      simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hspan,
      v.intValuation_if_neg hr, WithZero.log_exp]
    ring
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 K)) x
  have hn : n ≠ 0 := by
    intro hn
    apply hx
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : algebraMap (𝓞 K) K n ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hmapd : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 K) K) (by simpa using h))
  have hval : v.valuation K x = v.intValuation n / v.intValuation (d : 𝓞 K) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    hdiv (algebraMap (𝓞 K) K n) (algebraMap (𝓞 K) K (d : 𝓞 K)) hmapn hmapd,
    hint n hn, hint (d : 𝓞 K) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 K) hd)]
  ring

/-!
The principal-unit residue bridge has this exact signature:
```
theorem qs_nq0_residue_eq_one_of_valuation_sub_one_lt_one
    (v : FinPlace K) (x : K)
    (hx : v.valuation K (x - 1) < 1) :
    residue v x = 1
```
-/

/-- A global element congruent to one in the local valuation has residue one. -/
theorem qs_nq0_residue_eq_one_of_valuation_sub_one_lt_one
    (v : FinPlace K) (x : K)
    (hx : v.valuation K (x - 1) < 1) :
    residue v x = 1 := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hxval : v.valuation K x = 1 := by
    have h := (v.valuation K).map_eq_of_sub_lt (x := (1 : K)) (y := x)
      (by simpa only [map_one] using hx)
    simpa only [map_one] using h
  unfold residue
  split_ifs with h
  · have hdv : v.valuation K (algebraMap (𝓞 K) K h.choose.2) = 1 :=
      v.valuation_eq_one_iff_notMem.mpr h.choose_spec.1
    have hdq : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 :=
      (not_congr Ideal.Quotient.eq_zero_iff_mem).mpr h.choose_spec.1
    have hdiff : algebraMap (𝓞 K) K (h.choose.1 - h.choose.2) =
        (x - 1) * algebraMap (𝓞 K) K h.choose.2 := by
      rw [map_sub, ← h.choose_spec.2]
      ring
    have hmem : h.choose.1 - h.choose.2 ∈ v.asIdeal := by
      apply (v.valuation_lt_one_iff_mem (K := K) _).mp
      change v.valuation K (algebraMap (𝓞 K) K (h.choose.1 - h.choose.2)) < 1
      rw [hdiff, map_mul, hdv, mul_one]
      exact hx
    have hquot : Ideal.Quotient.mk v.asIdeal h.choose.1 =
        Ideal.Quotient.mk v.asIdeal h.choose.2 := by
      apply sub_eq_zero.mp
      rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    rw [hquot]
    exact mul_inv_cancel₀ hdq
  · obtain ⟨n, d, hnd⟩ :=
      v.exists_primeCompl_mul_eq_of_integer x (le_of_eq hxval)
    exact (h ⟨(n, (d : 𝓞 K)), d.property, hnd⟩).elim

/-!
The sextic residue-one step has this exact signature:
```
theorem qs_nq0_chiAlg_eq_one_of_residue_one
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x = 1) :
    chiAlg v x = 1
```
-/

/-- Away from six, residue one forces the sextic residue symbol to be one. -/
theorem qs_nq0_chiAlg_eq_one_of_residue_one
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x = 1) :
    chiAlg v x = 1 := by
  classical
  obtain ⟨hcop, hnorm⟩ := coprime_six_of_not_mem_six v h6
  unfold chiAlg
  split_ifs with h
  · apply Ideal.rootsOfUnityMapQuot_injective (I := v.asIdeal) 6 hnorm hcop
    apply Units.ext
    change Ideal.Quotient.mk v.asIdeal ((h.choose : (𝓞 K)ˣ) : 𝓞 K) =
      Ideal.Quotient.mk v.asIdeal ((1 : (𝓞 K)ˣ) : 𝓞 K)
    simpa only [hx, one_pow, Units.val_one, map_one] using h.choose_spec
  · rfl

/-!
The exact sextic-symbol reduction has this signature:
```
theorem qs_nq0_chiAlg_reduction (D : FieldData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal ((chiAlg v x : (𝓞 K)ˣ) : 𝓞 K) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
```
-/

/-- At a unit away from six, the chosen sextic symbol has its defining reduction. -/
theorem qs_nq0_chiAlg_reduction (D : FieldData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal ((chiAlg v x : (𝓞 K)ˣ) : 𝓞 K) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨hcop, hne1⟩ := coprime_six_of_not_mem_six v h6
  have hdvd6 := six_dvd_absNorm_sub_one D v h6
  have hζ6 : IsPrimitiveRoot (D.ζ12 ^ 2) 6 :=
    D.hζ12.pow_of_dvd (p := 2) (by decide) (by decide)
  have hprim := hζ6.toInteger_isPrimitiveRoot.idealQuotient_mk
    (I := v.asIdeal) hne1 hcop
  let r : (𝓞 K ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
  have hr_pow : (residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, Nat.mul_div_cancel' hdvd6]
    have hcoe : (r : 𝓞 K ⧸ v.asIdeal) ^ (Ideal.absNorm v.asIdeal - 1) =
        ((r ^ (Ideal.absNorm v.asIdeal - 1) : (𝓞 K ⧸ v.asIdeal)ˣ) :
          𝓞 K ⧸ v.asIdeal) := (Units.val_pow_eq_pow_val r _).symm
    have hcard : Nat.card (𝓞 K ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
      rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    have hr : r ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hr_eq : (r : 𝓞 K ⧸ v.asIdeal) = residue v x := rfl
    rw [← hr_eq, hcoe, hr, Units.val_one]
  obtain ⟨i, _, heq⟩ := hprim.eq_pow_of_pow_eq_one hr_pow
  have hζ_pow : (hζ6.toInteger ^ i) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ6.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  let ζ : rootsOfUnity 6 (𝓞 K) := rootsOfUnity.mkOfPowEq (hζ6.toInteger ^ i) hζ_pow
  have hex : ∃ z : rootsOfUnity 6 (𝓞 K),
      Ideal.Quotient.mk v.asIdeal ((z : (𝓞 K)ˣ) : 𝓞 K) =
        residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    refine ⟨ζ, ?_⟩
    have hcoe : ((ζ : (𝓞 K)ˣ) : 𝓞 K) = hζ6.toInteger ^ i :=
      rootsOfUnity.coe_mkOfPowEq hζ_pow
    rw [hcoe, map_pow]
    exact heq
  rw [chiAlg, dif_pos hex]
  exact hex.choose_spec

/-!
The cube reduction has this exact signature:
```
theorem qs_nq0_chiAlg_cube_reduction (D : FieldData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal (((chiAlg v x : (𝓞 K)ˣ) : 𝓞 K) ^ 3) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 2)
```
-/

/-- The cubed sextic symbol reduces to the quadratic residue power. -/
theorem qs_nq0_chiAlg_cube_reduction (D : FieldData K)
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal)
    (x : K) (hx : residue v x ≠ 0) :
    Ideal.Quotient.mk v.asIdeal (((chiAlg v x : (𝓞 K)ˣ) : 𝓞 K) ^ 3) =
      residue v x ^ ((Ideal.absNorm v.asIdeal - 1) / 2) := by
  have hdiv : 3 * ((Ideal.absNorm v.asIdeal - 1) / 6) =
      (Ideal.absNorm v.asIdeal - 1) / 2 := by
    obtain ⟨k, hk⟩ := six_dvd_absNorm_sub_one D v h6
    rw [hk, Nat.mul_div_cancel_left _ (by decide : 6 > 0)]
    have he : 6 * k = 2 * (3 * k) := by omega
    rw [he, Nat.mul_div_cancel_left _ (by decide : 2 > 0)]
  rw [map_pow, qs_nq0_chiAlg_reduction D v h6 x hx, ← pow_mul,
    mul_comm ((Ideal.absNorm v.asIdeal - 1) / 6) 3, hdiv]

/-!
The integral-residue bridge has this exact signature:
```
theorem qs_nq0_residue_algebraMap (v : FinPlace K) (x : 𝓞 K) :
    residue v (algebraMap (𝓞 K) K x) = Ideal.Quotient.mk v.asIdeal x
```
-/

/-- The residue of an integral element is its image in the residue field. -/
theorem qs_nq0_residue_algebraMap (v : FinPlace K) (x : 𝓞 K) :
    residue v (algebraMap (𝓞 K) K x) = Ideal.Quotient.mk v.asIdeal x := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  unfold residue
  split_ifs with h
  · have hdq : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 :=
      (not_congr Ideal.Quotient.eq_zero_iff_mem).mpr h.choose_spec.1
    have hn : h.choose.1 = x * h.choose.2 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [← h.choose_spec.2, map_mul]
    rw [hn, map_mul, mul_assoc, mul_inv_cancel₀ hdq, mul_one]
  · exact (h ⟨(x, 1), v.isPrime.one_notMem, by simp⟩).elim

/-!
The lifted quadratic-nonresidue step has this exact signature:
```
theorem qs_nq0_residue_quadratic_nontrivial
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal) :
    ∃ b : Kˣ, v.valuation K (b : K) = 1 ∧
      residue v (b : K) ^ ((Ideal.absNorm v.asIdeal - 1) / 2) ≠ 1
```
-/

/-- Away from six, a residue-field nonsquare lifts to a global valuation-one unit. -/
theorem qs_nq0_residue_quadratic_nontrivial
    (v : FinPlace K) (h6 : (6 : 𝓞 K) ∉ v.asIdeal) :
    ∃ b : Kˣ, v.valuation K (b : K) = 1 ∧
      residue v (b : K) ^ ((Ideal.absNorm v.asIdeal - 1) / 2) ≠ 1 := by
  classical
  let : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  have hchar : ringChar (𝓞 K ⧸ v.asIdeal) ≠ 2 := by
    intro hchar
    have htwo : (2 : 𝓞 K ⧸ v.asIdeal) = 0 :=
      (ringChar.spec (𝓞 K ⧸ v.asIdeal) 2).mpr (by rw [hchar])
    have hmem : (2 : 𝓞 K) ∈ v.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_ofNat] using htwo)
    apply h6
    have hsix : (6 : 𝓞 K) = 3 * 2 := by norm_num
    rw [hsix]
    exact Ideal.mul_mem_left _ _ hmem
  obtain ⟨t, ht⟩ := quadraticChar_exists_neg_one (F := 𝓞 K ⧸ v.asIdeal) hchar
  have ht0 : t ≠ 0 := by
    intro hzero
    rw [hzero, quadraticChar_zero] at ht
    norm_num at ht
  have hcard : Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hdiv : Fintype.card (𝓞 K ⧸ v.asIdeal) / 2 =
      (Ideal.absNorm v.asIdeal - 1) / 2 := by
    have hodd := FiniteField.odd_card_of_char_ne_two hchar
    omega
  have hpow : t ^ ((Ideal.absNorm v.asIdeal - 1) / 2) ≠ 1 := by
    have hp := quadraticChar_eq_pow_of_char_ne_two' hchar t
    rw [ht, Int.cast_neg, Int.cast_one, hdiv] at hp
    rw [← hp]
    exact Ring.neg_one_ne_one_of_char_ne_two hchar
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) t
  have hc0 : c ≠ 0 := by
    intro hzero
    apply ht0
    rw [← hc, hzero, map_zero]
  have hmap : algebraMap (𝓞 K) K c ≠ 0 := by
    intro hzero
    exact hc0 ((IsFractionRing.injective (𝓞 K) K) (by simpa using hzero))
  let b : Kˣ := Units.mk0 (algebraMap (𝓞 K) K c) hmap
  have hb : residue v (b : K) = t := by
    change residue v (algebraMap (𝓞 K) K c) = t
    rw [qs_nq0_residue_algebraMap, hc]
  refine ⟨b, qs_nq0_residue_ne_zero_iff_valuation_one v (b : K) |>.mp ?_, ?_⟩
  · rwa [hb]
  · rwa [hb]

end ArtinPrimitiveRoots.A2
