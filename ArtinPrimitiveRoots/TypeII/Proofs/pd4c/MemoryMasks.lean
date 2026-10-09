import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- Endpoint hit damping and distinct finite masks preserve a weighted kernel bound. -/
theorem finite_weighted_damped_rectangular_bound {α : Type*} [DecidableEq α]
    (U I O : Finset α) (hI : I ⊆ U) (hO : O ⊆ U)
    (m ν : α → ℝ) (hm : ∀ s ∈ U, 0 ≤ m s)
    (k : α → α → ℂ) (ρ R : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hits : α → ℕ)
    (hk : ∀ d e : α → ℂ,
      (∀ s ∈ U, ‖d s‖ ≤ 1) → (∀ s ∈ U, ‖e s‖ ≤ 1) →
      ∀ g : α → ℂ,
      (∑ s ∈ U, m s*‖d s*(∑ t ∈ U, k s t*(ν t : ℂ)*e t*g t)‖^2) ≤
        R^2*(∑ t ∈ U, m t*‖g t‖^2))
    (f : α → ℂ) :
    (∑ s ∈ O, m s*‖(ρ^hits s : ℂ)*
      (∑ t ∈ I, k s t*(ν t : ℂ)*(ρ^hits t : ℂ)*f t)‖^2) ≤
      R^2*(∑ t ∈ I, m t*‖f t‖^2) := by
  let d : α → ℂ := fun s => (ρ^hits s : ℂ)
  let g : α → ℂ := fun t => if t ∈ I then f t else 0
  have hd (s : α) : ‖d s‖ ≤ 1 := by
    simpa only [d, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hρ0 (hits s))] using
      (pow_le_one₀ hρ0 hρ1 : ρ ^ hits s ≤ 1)
  have hrow (s : α) : (∑ t ∈ U, k s t*(ν t : ℂ)*d t*g t) =
      ∑ t ∈ I, k s t*(ν t : ℂ)*d t*f t := by
    calc
      _ = ∑ t ∈ I, k s t*(ν t : ℂ)*d t*g t :=
        (Finset.sum_subset hI (fun t ht hnot => by
          simp only [g, if_neg hnot, mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun t ht => by simp only [g, if_pos ht])
  have henergy : (∑ t ∈ U, m t*‖g t‖^2) = ∑ t ∈ I, m t*‖f t‖^2 := by
    calc
      _ = ∑ t ∈ I, m t*‖g t‖^2 :=
        (Finset.sum_subset hI (fun t ht hnot => by
          simp only [g, if_neg hnot, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero])).symm
      _ = _ := Finset.sum_congr rfl (fun t ht => by simp only [g, if_pos ht])
  calc
    _ = ∑ s ∈ O, m s*‖d s*(∑ t ∈ U, k s t*(ν t : ℂ)*d t*g t)‖^2 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hrow s]
    _ ≤ ∑ s ∈ U, m s*‖d s*(∑ t ∈ U, k s t*(ν t : ℂ)*d t*g t)‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hO (fun s hs hnot =>
        mul_nonneg (hm s hs) (sq_nonneg _))
    _ ≤ R^2*(∑ t ∈ U, m t*‖g t‖^2) :=
      hk d d (fun s hs => hd s) (fun s hs => hd s) g
    _ = _ := by rw [henergy]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
