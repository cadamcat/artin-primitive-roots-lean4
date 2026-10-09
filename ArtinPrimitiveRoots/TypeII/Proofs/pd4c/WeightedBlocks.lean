import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- A supported finite kernel retains its weighted norm bound when its blocks are assembled. -/
theorem finite_weighted_block_kernel_bound {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (μ : ι → ℝ) (outClass inClass : ι → κ)
    (k : ι → ι → ℂ) (R : ℝ) (f : ι → ℂ)
    (hsupport : ∀ u ∈ I, ∀ v ∈ I, outClass u ≠ inClass v → k u v = 0)
    (hblocks : ∀ b ∈ I.image outClass ∪ I.image inClass,
      (∑ u ∈ I.filter (fun u => outClass u = b),
        μ u*‖∑ v ∈ I.filter (fun v => inClass v = b), k u v*(μ v : ℂ)*f v‖^2) ≤
      R^2*(∑ v ∈ I.filter (fun v => inClass v = b), μ v*‖f v‖^2)) :
    (∑ u ∈ I, μ u*‖∑ v ∈ I, k u v*(μ v : ℂ)*f v‖^2) ≤
      R^2*(∑ v ∈ I, μ v*‖f v‖^2) := by
  let B : Finset κ := I.image outClass ∪ I.image inClass
  have hout (u : ι) (hu : u ∈ I) : outClass u ∈ B :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have hin (v : ι) (hv : v ∈ I) : inClass v ∈ B :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have hrow (u : ι) (hu : u ∈ I) (b : κ) (hb : outClass u = b) :
      (∑ v ∈ I, k u v*(μ v : ℂ)*f v) =
        ∑ v ∈ I.filter (fun v => inClass v = b), k u v*(μ v : ℂ)*f v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hnot
    have hne : outClass u ≠ inClass v := by
      intro heq
      exact hnot (Finset.mem_filter.mpr ⟨hv, heq.symm.trans hb⟩)
    rw [hsupport u hu v hv hne, zero_mul, zero_mul]
  calc
    _ = ∑ b ∈ B, ∑ u ∈ I.filter (fun u => outClass u = b),
        μ u*‖∑ v ∈ I, k u v*(μ v : ℂ)*f v‖^2 :=
      (Finset.sum_fiberwise_of_maps_to hout
        (fun u => μ u*‖∑ v ∈ I, k u v*(μ v : ℂ)*f v‖^2)).symm
    _ = ∑ b ∈ B, ∑ u ∈ I.filter (fun u => outClass u = b),
        μ u*‖∑ v ∈ I.filter (fun v => inClass v = b), k u v*(μ v : ℂ)*f v‖^2 := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro u hu
      rw [hrow u (Finset.mem_filter.mp hu).1 b (Finset.mem_filter.mp hu).2]
    _ ≤ ∑ b ∈ B, R^2*(∑ v ∈ I.filter (fun v => inClass v = b), μ v*‖f v‖^2) :=
      Finset.sum_le_sum (fun b hb => hblocks b hb)
    _ = R^2*(∑ b ∈ B, ∑ v ∈ I.filter (fun v => inClass v = b), μ v*‖f v‖^2) := by
      rw [Finset.mul_sum]
    _ = _ := congrArg (fun t : ℝ => R^2*t)
      (Finset.sum_fiberwise_of_maps_to hin (fun v => μ v*‖f v‖^2))

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
