import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.GeometricSum
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CircleHarmonic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Separated phases give a logarithmic row bound for finite geometric sums. -/
theorem separated_geometric_row_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (d N : ℕ) (hd : 2 ≤ d)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      1 / (2 * (d : ℝ)) ≤ circleDistance (φ i - φ j)) :
    (∑ i ∈ T, ‖∑ n ∈ Finset.range N,
      additiveCharacter (φ i * (n : ℝ))‖) ≤
    (N : ℝ) + 32 * (d : ℝ) * (1 + Real.log (4 * (d : ℝ))) := by
  let H : α → ℝ := fun i => if circleDistance (φ i) = 0 then (N : ℝ) / 2
    else min ((N : ℝ) / 2) (1 / circleDistance (φ i))
  have htrivial (i : α) :
      ‖∑ n ∈ Finset.range N, additiveCharacter (φ i * (n : ℝ))‖ ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖additiveCharacter (φ i * (n : ℝ))‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [pd4c_character_norm, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
  have hpoint (i : α) :
      ‖∑ n ∈ Finset.range N, additiveCharacter (φ i * (n : ℝ))‖ ≤ 2 * H i := by
    by_cases hz : circleDistance (φ i) = 0
    · dsimp only [H]
      rw [if_pos hz]
      linarith only [htrivial i]
    · have hnonneg : 0 ≤ circleDistance (φ i) := by
        rw [pd4c_circleDistance_eq_round]
        exact abs_nonneg _
      have hpos : 0 < circleDistance (φ i) := lt_of_le_of_ne hnonneg (Ne.symm hz)
      have hgeo := pd4c_geometric_sum_norm_le (φ i) N hpos
      have hmin :
          ‖∑ n ∈ Finset.range N, additiveCharacter (φ i * (n : ℝ))‖ / 2 ≤
          min ((N : ℝ) / 2) (1 / circleDistance (φ i)) := by
        apply le_min
        · exact div_le_div_of_nonneg_right (htrivial i) (by norm_num)
        · calc
            _ ≤ (2 / circleDistance (φ i)) / 2 :=
              div_le_div_of_nonneg_right hgeo (by norm_num)
            _ = _ := by ring
      dsimp only [H]
      rw [if_neg hz]
      linarith only [hmin]
  have hsum := circle_inverse_log_bound T φ d ((N : ℝ) / 2) hd (by positivity) hsep
  change (∑ i ∈ T, H i) ≤ (N : ℝ) / 2 +
    16 * (d : ℝ) * (1 + Real.log (4 * (d : ℝ))) at hsum
  calc
    _ ≤ ∑ i ∈ T, 2 * H i := Finset.sum_le_sum fun i hi => hpoint i
    _ = 2 * (∑ i ∈ T, H i) := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * ((N : ℝ) / 2 +
        16 * (d : ℝ) * (1 + Real.log (4 * (d : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
