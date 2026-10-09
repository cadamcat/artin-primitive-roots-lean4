import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

/-- A summable common mode bound controls the square mass of the reconstructed
finite row, including convergence in each coordinate. -/
theorem finite_row_tsum_l2 {M : Type*} [Fintype M]
    (g : ℤ → M → ℂ) (bound : ℤ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hbound : ∀ j, 0 ≤ bound j) (hsum : Summable bound)
    (hrow : ∀ j, (∑ m : M, ‖g j m‖ ^ 2) ≤ (bound j) ^ 2 * R) :
    (∀ m, Summable (fun j : ℤ => g j m)) ∧
      (∑ m : M, ‖∑' j : ℤ, g j m‖ ^ 2) ≤
        (∑' j : ℤ, bound j) ^ 2 * R := by
  let G (j : ℤ) : EuclideanSpace ℂ M := WithLp.toLp 2 (g j)
  have hnorm (j : ℤ) : ‖G j‖ ≤ bound j * Real.sqrt R := by
    have hsquare : ‖G j‖ ^ 2 ≤ (bound j * Real.sqrt R) ^ 2 := by
      simpa only [EuclideanSpace.norm_sq_eq, G, mul_pow, Real.sq_sqrt hR] using hrow j
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hbound j) (Real.sqrt_nonneg _))).mp hsquare
  have hmajor : Summable (fun j : ℤ => bound j * Real.sqrt R) := hsum.mul_right _
  have hG : Summable G := hmajor.of_norm_bounded hnorm
  let eval (m : M) : EuclideanSpace ℂ M →L[ℂ] ℂ := PiLp.proj 2 (fun _ : M => ℂ) m
  have hcoord (m : M) : (∑' j : ℤ, G j) m = ∑' j : ℤ, g j m := by
    change eval m (∑' j : ℤ, G j) = ∑' j : ℤ, eval m (G j)
    exact (eval m).map_tsum hG
  have htotal : ‖∑' j : ℤ, G j‖ ≤ (∑' j : ℤ, bound j) * Real.sqrt R := by
    calc
      _ ≤ ∑' j : ℤ, bound j * Real.sqrt R :=
        tsum_of_norm_bounded hmajor.hasSum hnorm
      _ = _ := tsum_mul_right
  refine ⟨?_, ?_⟩
  · intro m
    change Summable (fun j : ℤ => eval m (G j))
    exact (eval m).summable hG
  · calc
      _ = ‖∑' j : ℤ, G j‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        exact Finset.sum_congr rfl fun m _ => by rw [hcoord]
      _ ≤ ((∑' j : ℤ, bound j) * Real.sqrt R) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (tsum_nonneg hbound)
          (Real.sqrt_nonneg _))).mpr htotal
      _ = _ := by rw [mul_pow, Real.sq_sqrt hR]

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
