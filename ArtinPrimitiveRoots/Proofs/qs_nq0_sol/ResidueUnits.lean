import ArtinPrimitiveRoots.A1.Residue

/-!
# Residue and local-unit conditions

The next bridge, in this module's context, is:
```
theorem qs_nq0_residue_ne_zero_iff_valuation_one (v : FinPlace K) (x : K) :
    residue v x ≠ 0 ↔ v.valuation K x = 1
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

end ArtinPrimitiveRoots.A2
