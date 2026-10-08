import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Circle

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical
open ArtinPrimitiveRoots.TypeII

theorem pd4c_character_add (a b : ℝ) :
    additiveCharacter (a + b) = additiveCharacter a * additiveCharacter b := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pd4c_character_int (k : ℤ) : additiveCharacter (k : ℝ) = 1 := by
  unfold additiveCharacter
  push_cast
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  congr 1
  ring

theorem pd4c_character_add_int (t : ℝ) (k : ℤ) :
    additiveCharacter (t + (k : ℝ)) = additiveCharacter t := by
  rw [pd4c_character_add, pd4c_character_int, mul_one]

theorem pd4c_character_norm (t : ℝ) : ‖additiveCharacter t‖ = 1 := by
  unfold additiveCharacter
  rw [Complex.norm_exp]
  simp

/-- The geometric-sum bound, with the nearest-integer distance as its separation parameter. -/
theorem pd4c_geometric_sum_norm_le (t : ℝ) (N : ℕ) (hδ : 0 < circleDistance t) :
    ‖∑ n ∈ Finset.range N, additiveCharacter (t * (n : ℝ))‖ ≤ 2 / circleDistance t := by
  let a := Int.fract t
  have hlo : circleDistance t ≤ a := by
    rw [pd4c_circleDistance_eq_round, abs_sub_round_eq_min]
    exact min_le_left _ _
  have hhi : a ≤ 1 - circleDistance t := by
    have h : circleDistance t ≤ 1 - a := by
      rw [pd4c_circleDistance_eq_round, abs_sub_round_eq_min]
      exact min_le_right _ _
    linarith
  let f : ℕ → ℝ := fun n => a * (n : ℝ)
  have hdiff (n : ℕ) : f (n + 1) - f n = a := by dsimp [f]; push_cast; ring
  have hder := ArtinPrimitiveRoots.Ext.TypeIIInputs.derivative_test f N (circleDistance t) hδ
    (fun n hn => by rw [hdiff]; exact hlo)
    (fun n hn => by rw [hdiff]; exact hhi)
    (by intro n hn m hm hnm; dsimp only; rw [hdiff, hdiff])
  have hchar (n : ℕ) : additiveCharacter (t * (n : ℝ)) = additiveCharacter (f n) := by
    have harg : t * (n : ℝ) = a * (n : ℝ) + (((⌊t⌋ : ℤ) * (n : ℤ) : ℤ) : ℝ) := by
      push_cast
      have h := Int.fract_add_floor t
      dsimp [a]
      nlinarith
    rw [harg, pd4c_character_add_int]
  simpa only [hchar] using hder

end

end ArtinPrimitiveRoots.TypeII.PD
