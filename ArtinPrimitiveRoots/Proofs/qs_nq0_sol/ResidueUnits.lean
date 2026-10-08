import ArtinPrimitiveRoots.A1.Residue

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

end ArtinPrimitiveRoots.A2
