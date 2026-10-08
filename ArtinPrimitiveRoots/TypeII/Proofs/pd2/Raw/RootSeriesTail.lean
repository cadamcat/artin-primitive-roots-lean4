import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootEulerConstant

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_inverse_square_tail (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ, 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let f := fun j : ℕ => 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2
  have hpoint : ∀ j : ℕ, f j ≤ 1 / ((N + j : ℕ) : ℝ) - 1 / ((N + (j + 1) : ℕ) : ℝ) := by
    intro j
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
    have hjR : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    dsimp [f]
    push_cast
    have hA : (N : ℝ) + j ≠ 0 := by positivity
    have hB : (N : ℝ) + 1 + j ≠ 0 := by positivity
    field_simp
    nlinarith
  have hpartial : ∀ M : ℕ, (∑ j ∈ Finset.range M, f j) ≤ 1 / (N : ℝ) := by
    intro M
    calc
      _ ≤ ∑ j ∈ Finset.range M, (1 / ((N + j : ℕ) : ℝ) - 1 / ((N + (j + 1) : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun j hj => hpoint j
      _ = 1 / (N : ℝ) - 1 / ((N + M : ℕ) : ℝ) := by
        simpa using Finset.sum_range_sub' (fun j : ℕ => 1 / ((N + j : ℕ) : ℝ)) M
      _ ≤ _ := sub_le_self _ (by positivity)
  exact Real.tsum_le_of_sum_range_le (fun j => by positivity) hpartial

lemma pd2a_rootEulerCoefficient_norm (S n : ℕ) :
    ‖pd2a_rootEulerCoefficient S n‖ ≤ 1 / (n : ℝ) ^ 2 := by
  unfold pd2a_rootEulerCoefficient
  split_ifs
  · have hnAbs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    simp only [norm_div, Real.norm_eq_abs, abs_pow, hnAbs]
    have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    exact div_le_div_of_nonneg_right hμ (sq_nonneg _)
  · rw [norm_zero]
    exact div_nonneg (by norm_num) (sq_nonneg _)

lemma pd2a_rootEuler_prefix_error (S N : ℕ) (hS : 0 < S) (hN : 0 < N) :
    |pd2a_rootEulerConstant S - ∑ n ∈ Finset.range (N + 1), pd2a_rootEulerCoefficient S n| ≤ 1 / (N : ℝ) := by
  let f := fun j : ℕ => pd2a_rootEulerCoefficient S (N + 1 + j)
  let g := fun j : ℕ => 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2
  have hPoint : ∀ j, ‖f j‖ ≤ g j := fun j => pd2a_rootEulerCoefficient_norm S _
  have hg : Summable g := by
    have hSeries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact hSeries.comp_injective (fun a b h => by omega)
  have hfn : Summable (fun j => ‖f j‖) := hg.of_nonneg_of_le (fun j => norm_nonneg _) hPoint
  have hf := pd2a_rootEuler_summable S hS
  have hEq : pd2a_rootEulerConstant S - ∑ n ∈ Finset.range (N + 1), pd2a_rootEulerCoefficient S n = ∑' j : ℕ, f j := by
    have h := hf.sum_add_tsum_nat_add (N + 1)
    have h' : (∑ n ∈ Finset.range (N + 1), pd2a_rootEulerCoefficient S n) + (∑' j : ℕ, f j) = pd2a_rootEulerConstant S := by
      simpa only [pd2a_rootEulerConstant, f, Nat.add_comm] using h
    linarith
  rw [hEq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' j : ℕ, ‖f j‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' j : ℕ, g j := hfn.tsum_le_tsum hPoint hg
    _ ≤ _ := pd2a_inverse_square_tail N hN

end ArtinPrimitiveRoots.TypeII.PD
