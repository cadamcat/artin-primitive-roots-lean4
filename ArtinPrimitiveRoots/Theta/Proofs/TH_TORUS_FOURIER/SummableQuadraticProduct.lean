import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

private def quadraticWeight (k : ℤ) : ℝ := (1 + (2 * Real.pi * (k : ℝ)) ^ 2)⁻¹

private theorem summable_quadratic_frequency : Summable quadraticWeight := by
  change Summable (fun k : ℤ => (1 + (2 * Real.pi * (k : ℝ)) ^ 2)⁻¹)
  have hsq : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hmajor : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 1 / (k : ℝ) ^ 2) :=
    hsq.congr_cofinite (by
      filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with k hk
      simp only [ite_eq_right hk])
  have hc : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hc2 : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi - 1)]
  apply Summable.of_nonneg_of_le (fun k => by positivity) ?_ hmajor
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [ite_eq_right hk]
    have hpos : 0 < (k : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hk)
    have hle : (k : ℝ) ^ 2 ≤ 1 + (2 * Real.pi * (k : ℝ)) ^ 2 := by
      calc
        (k : ℝ) ^ 2 ≤ (2 * Real.pi) ^ 2 * (k : ℝ) ^ 2 := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hc2 (sq_nonneg (k : ℝ))
        _ = (2 * Real.pi * (k : ℝ)) ^ 2 := by ring
        _ ≤ 1 + (2 * Real.pi * (k : ℝ)) ^ 2 := by linarith
    simpa only [one_div] using one_div_le_one_div_of_le hpos hle

/-- The inverse-quadratic frequency majorant is summable in every finite
dimension, including the empty set of coordinates. -/
theorem summable_quadratic_product (n : ℕ) :
    Summable (fun k : Fin n → ℤ =>
      ∏ i : Fin n, (1 + (2 * Real.pi * (k i : ℝ)) ^ 2)⁻¹) := by
  change Summable (fun k : Fin n → ℤ => ∏ i : Fin n, quadraticWeight (k i))
  induction n with
  | zero =>
      exact Summable.of_finite
  | succ n ih =>
      have hpos1 : ∀ k : ℤ, 0 ≤ quadraticWeight k := by
        intro k
        unfold quadraticWeight
        positivity
      have hposn : ∀ k : Fin n → ℤ,
          0 ≤ ∏ i : Fin n, quadraticWeight (k i) := by
        intro k
        apply Finset.prod_nonneg
        intro i _
        exact hpos1 (k i)
      have hpair : Summable (fun p : ℤ × (Fin n → ℤ) =>
          quadraticWeight p.1 * ∏ i : Fin n, quadraticWeight (p.2 i)) :=
        Summable.mul_of_nonneg (f := quadraticWeight)
          (g := fun k : Fin n → ℤ => ∏ i : Fin n, quadraticWeight (k i))
          summable_quadratic_frequency ih hpos1 hposn
      have hinj : Function.Injective (fun k : Fin (n + 1) → ℤ =>
          (k 0, fun j : Fin n => k j.succ)) := by
        intro a b h
        funext i
        refine Fin.cases ?_ ?_ i
        · exact congrArg Prod.fst h
        · intro j
          exact congrFun (congrArg Prod.snd h) j
      apply (hpair.comp_injective hinj).congr
      intro k
      change quadraticWeight (k 0) *
        (∏ j : Fin n, quadraticWeight (k j.succ)) = _
      exact (Fin.prod_univ_succ (fun i : Fin (n + 1) => quadraticWeight (k i))).symm

end ArtinPrimitiveRoots.Proofs.thsol_torusf
