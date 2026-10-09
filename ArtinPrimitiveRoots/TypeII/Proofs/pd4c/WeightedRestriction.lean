import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- Distinct input and output restrictions retain a common finite weighted kernel norm bound. -/
theorem finite_weighted_rectangular_kernel_bound {ι : Type*} [DecidableEq ι]
    (I O J : Finset ι) (hO : O ⊆ I) (hJ : J ⊆ I)
    (μ : ι → ℝ) (hμ : ∀ u ∈ I, 0 ≤ μ u)
    (k : ι → ι → ℂ) (d e : ι → ℂ) (R : ℝ)
    (hk : ∀ g : ι → ℂ,
      (∑ u ∈ I, μ u*‖d u*(∑ v ∈ I, k u v*(μ v : ℂ)*e v*g v)‖^2) ≤
        R^2*(∑ v ∈ I, μ v*‖g v‖^2))
    (f : ι → ℂ) :
    (∑ u ∈ O, μ u*‖d u*(∑ v ∈ J, k u v*(μ v : ℂ)*e v*f v)‖^2) ≤
      R^2*(∑ v ∈ J, μ v*‖f v‖^2) := by
  let g : ι → ℂ := fun v => if v ∈ J then f v else 0
  have hrow (u : ι) : (∑ v ∈ I, k u v*(μ v : ℂ)*e v*g v) =
      ∑ v ∈ J, k u v*(μ v : ℂ)*e v*f v := by
    calc
      _ = ∑ v ∈ J, k u v*(μ v : ℂ)*e v*g v :=
        (Finset.sum_subset hJ (fun v hv hnot => by simp only [g, if_neg hnot, mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun v hv => by simp only [g, if_pos hv])
  have henergy : (∑ v ∈ I, μ v*‖g v‖^2) = ∑ v ∈ J, μ v*‖f v‖^2 := by
    calc
      _ = ∑ v ∈ J, μ v*‖g v‖^2 :=
        (Finset.sum_subset hJ (fun v hv hnot => by
          simp only [g, if_neg hnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun v hv => by simp only [g, if_pos hv])
  calc
    _ = ∑ u ∈ O, μ u*‖d u*(∑ v ∈ I, k u v*(μ v : ℂ)*e v*g v)‖^2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hrow u]
    _ ≤ ∑ u ∈ I, μ u*‖d u*(∑ v ∈ I, k u v*(μ v : ℂ)*e v*g v)‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hO (fun u hu hnot =>
        mul_nonneg (hμ u hu) (sq_nonneg _))
    _ ≤ R^2*(∑ v ∈ I, μ v*‖g v‖^2) := hk g
    _ = _ := by rw [henergy]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
