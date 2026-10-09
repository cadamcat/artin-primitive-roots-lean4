import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- Finite fibre bounds assemble without changing the normalization of the row coefficients. -/
theorem finite_fibre_kernel_bound {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (I : Finset α) (μ : α → ℝ) (cls : α → κ)
    (k : α → α → ℂ) (R : ℝ) (f : α → ℂ)
    (hsupport : ∀ u ∈ I, ∀ v ∈ I, cls u ≠ cls v → k u v = 0)
    (hblocks : ∀ b ∈ I.image cls,
      (∑ u ∈ I.filter (fun u => cls u = b),
        μ u*‖∑ v ∈ I.filter (fun v => cls v = b), k u v*f v‖^2) ≤
      R^2*(∑ v ∈ I.filter (fun v => cls v = b), μ v*‖f v‖^2)) :
    (∑ u ∈ I, μ u*‖∑ v ∈ I, k u v*f v‖^2) ≤
      R^2*(∑ v ∈ I, μ v*‖f v‖^2) := by
  let B : Finset κ := I.image cls
  have hmap (u : α) (hu : u ∈ I) : cls u ∈ B :=
    Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hrow (u : α) (hu : u ∈ I) (b : κ) (hb : cls u = b) :
      (∑ v ∈ I, k u v*f v) = ∑ v ∈ I.filter (fun v => cls v = b), k u v*f v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hnot
    have hne : cls u ≠ cls v := by
      intro heq
      exact hnot (Finset.mem_filter.mpr ⟨hv, heq.symm.trans hb⟩)
    rw [hsupport u hu v hv hne, zero_mul]
  calc
    _ = ∑ b ∈ B, ∑ u ∈ I.filter (fun u => cls u = b),
        μ u*‖∑ v ∈ I, k u v*f v‖^2 :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun u => μ u*‖∑ v ∈ I, k u v*f v‖^2)).symm
    _ = ∑ b ∈ B, ∑ u ∈ I.filter (fun u => cls u = b),
        μ u*‖∑ v ∈ I.filter (fun v => cls v = b), k u v*f v‖^2 := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro u hu
      rw [hrow u (Finset.mem_filter.mp hu).1 b (Finset.mem_filter.mp hu).2]
    _ ≤ ∑ b ∈ B, R^2*(∑ v ∈ I.filter (fun v => cls v = b), μ v*‖f v‖^2) :=
      Finset.sum_le_sum (fun b hb => hblocks b hb)
    _ = R^2*(∑ b ∈ B, ∑ v ∈ I.filter (fun v => cls v = b), μ v*‖f v‖^2) := by
      rw [Finset.mul_sum]
    _ = _ := congrArg (fun t : ℝ => R^2*t)
      (Finset.sum_fiberwise_of_maps_to hmap (fun v => μ v*‖f v‖^2))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
