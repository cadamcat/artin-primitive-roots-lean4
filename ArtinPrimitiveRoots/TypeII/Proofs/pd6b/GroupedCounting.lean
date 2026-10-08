import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- A weight constant on each finite group is the group count times its common value. -/
theorem grouped_weight_sum {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (T : Finset κ) (key : α → κ) (hkey : ∀ x ∈ S, key x ∈ T) (w : κ → ℝ) :
    (∑ x ∈ S, w (key x)) = ∑ k ∈ T, ((S.filter fun x => key x = k).card : ℝ) * w k := by
  have h := Finset.sum_fiberwise_of_maps_to' hkey w
  simpa only [Finset.sum_const, nsmul_eq_mul] using h.symm

/-- Group count upper bounds may be summed against nonnegative weights. -/
theorem grouped_weight_sum_upper {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (T : Finset κ) (key : α → κ) (hkey : ∀ x ∈ S, key x ∈ T)
    (w bound : κ → ℝ) (hw : ∀ k ∈ T, 0 ≤ w k)
    (hcount : ∀ k ∈ T, ((S.filter fun x => key x = k).card : ℝ) ≤ bound k) :
    (∑ x ∈ S, w (key x)) ≤ ∑ k ∈ T, bound k * w k := by
  rw [grouped_weight_sum S T key hkey w]
  exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hcount k hk) (hw k hk))

/-- A finite group may use any representative when the weight is constant on its fiber. -/
theorem grouped_constant_weight_sum {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (S : Finset α) (T : Finset κ) (key : α → κ) (hkey : ∀ x ∈ S, key x ∈ T)
    (f : α → ℝ) (repr : κ → α)
    (hconstant : ∀ x ∈ S, f x = f (repr (key x))) :
    (∑ x ∈ S, f x) = ∑ k ∈ T, ((S.filter fun x => key x = k).card : ℝ) * f (repr k) := by
  calc
    _ = ∑ x ∈ S, f (repr (key x)) := Finset.sum_congr rfl hconstant
    _ = _ := grouped_weight_sum S T key hkey (fun k => f (repr k))


end ArtinPrimitiveRoots.TypeII.PD
