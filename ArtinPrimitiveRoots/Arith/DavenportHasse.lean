import Mathlib

/-!
# Davenport–Hasse lifting for Jacobi sums

The multiplicative characters are pulled back along the field norm.
-/

namespace ArtinPrimitiveRoots.Arith

/-- Pull back a multiplicative character along the algebra norm. -/
noncomputable def normLift {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Module.Free k K]
    (χ : MulChar k ℂ) : MulChar K ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Algebra.norm k)))

/-- The norm pullback agrees with evaluation on the norm, including at zero. -/
@[simp] theorem normLift_apply {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [Module.Free k K]
    (χ : MulChar k ℂ) (x : K) : normLift χ x = χ (Algebra.norm k x) := by
  change MulChar.ofUnitHom (χ.toUnitHom.comp (Units.map (Algebra.norm k))) x = _
  by_cases hx : x = 0
  · subst x
    rw [MulChar.map_zero, Algebra.norm_zero, MulChar.map_zero]
  · have hxU : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hxU.unit_spec, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulChar.coe_toUnitHom,
      Units.coe_map]

theorem jacobiSum_lift {k K : Type*} [Field k] [Fintype k] [Field K] [Fintype K]
    [Algebra k K] (α β : MulChar k ℂ) (hα : α ≠ 1) (hβ : β ≠ 1)
    (hαβ : α * β ≠ 1) (hf : 1 ≤ Module.finrank k K) :
    jacobiSum (normLift (k := k) (K := K) α) (normLift (k := k) (K := K) β) =
      (-1 : ℂ) ^ (Module.finrank k K - 1) *
        jacobiSum α β ^ Module.finrank k K := by
  sorry

end ArtinPrimitiveRoots.Arith
