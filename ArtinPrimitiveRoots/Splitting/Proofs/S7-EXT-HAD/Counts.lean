import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Jensen

set_option autoImplicit false
open scoped BigOperators
open Classical Metric MeromorphicOn

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

def zeroOrderWeights (G : ℂ → ℂ) (z : ℂ) : ℕ :=
  if G z = 0 then analyticOrderNatAt G z else 0

/-- Jensen gives finite disk supports and a dyadic count majorant for order-one growth. -/
theorem entire_dyadic_zero_count (G : ℂ → ℂ) (hG : Differentiable ℂ G) (hG0 : G 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖G s‖ ≤ Real.exp (C * (‖s‖ + 1) * Real.log (‖s‖ + 2))) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ R : ℝ, 0 < R → Function.HasFiniteSupport
        (fun z : ℂ => if ‖z‖ ≤ R then (zeroOrderWeights G z : ℝ) else 0)) ∧
      ∀ n : ℕ,
        (∑' z : ℂ, if ‖z‖ ≤ (2 : ℝ) ^ (n + 1) then (zeroOrderWeights G z : ℝ) else 0) ≤
          A * ((n : ℝ) + 2) * (2 : ℝ) ^ (n + 1) := by
  classical
  obtain ⟨C, hC, hgrowth⟩ := hgrowth
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hGnorm : 0 < ‖G 0‖ := norm_pos_iff.mpr hG0
  let B : ℝ := |Real.log ‖G 0‖| / Real.log 2
  let A : ℝ := 6 * C + B + 1
  have hB : 0 ≤ B := div_nonneg (abs_nonneg _) hlog2.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_, ?_⟩
  · intro R _
    have hin : AnalyticOnNhd ℂ G (closedBall 0 R) := fun z _ => hG.analyticAt z
    let D := divisor G (closedBall 0 R)
    have hD : Function.HasFiniteSupport D :=
      (divisor G (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
    have horder (z : ℂ) (hz : ‖z‖ ≤ R) : D z = (analyticOrderNatAt G z : ℤ) := by
      have hzball : z ∈ closedBall (0 : ℂ) R := by simpa [mem_closedBall, dist_eq_norm] using hz
      simp only [D, hin.divisor_apply hzball]
      cases h : analyticOrderAt G z with
      | top => simp [analyticOrderNatAt, h]
      | coe n => simp [analyticOrderNatAt, h]
    apply hD.subset
    intro z hz
    change (if ‖z‖ ≤ R then (zeroOrderWeights G z : ℝ) else 0) ≠ 0 at hz
    change D z ≠ 0
    by_cases hzR : ‖z‖ ≤ R
    · by_cases hzG : G z = 0
      · have hz0 : (analyticOrderNatAt G z : ℝ) ≠ 0 := by
          simpa [zeroOrderWeights, hzR, hzG] using hz
        rw [horder z hzR]
        exact_mod_cast hz0
      · exact (hz (by simp [zeroOrderWeights, hzR, hzG])).elim
    · exact (hz (by simp [hzR])).elim
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  let R : ℝ := (2 : ℝ) ^ (n + 1)
  have hR : 0 < R := pow_pos (by norm_num) _
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  let U : Set ℂ := {z | G z = 0 ∧ ‖z‖ ≤ R}
  have hM : 1 ≤ Real.exp (C * (2 * R + 1) * Real.log (2 * R + 2)) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hGa : AnalyticOnNhd ℂ G (closedBall 0 (2 * R)) := fun z _ => hG.analyticAt z
  have hbound : ∀ z ∈ sphere (0 : ℂ) (2 * R),
      ‖G z‖ ≤ Real.exp (C * (2 * R + 1) * Real.log (2 * R + 2)) := by
    intro z hz
    have hn : ‖z‖ = 2 * R := by simpa [mem_sphere, dist_eq_norm] using hz
    simpa only [hn] using hgrowth z
  have hU : U ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    simpa [mem_closedBall, dist_eq_norm] using hz.2
  obtain ⟨_, hj⟩ := jensen_multiplicity_count
    (G := G) (c := 0) (r := R) (R := 2 * R)
    (M := Real.exp (C * (2 * R + 1) * Real.log (2 * R + 2))) (U := U)
    hR (by linarith) hM hGa hG0 hbound hU
  have hj' : (∑' z : ℂ, if ‖z‖ ≤ R then (zeroOrderWeights G z : ℝ) else 0) ≤
      Real.log (Real.exp (C * (2 * R + 1) * Real.log (2 * R + 2)) / ‖G 0‖) /
        Real.log (2 * R / R) := by
    convert hj using 1
    apply tsum_congr
    intro z
    by_cases hzG : G z = 0 <;> by_cases hzR : ‖z‖ ≤ R <;>
      simp [U, zeroOrderWeights, hzG, hzR]
  rw [show 2 * R / R = (2 : ℝ) by field_simp] at hj'
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hGnorm), Real.log_exp] at hj'
  have hlog : Real.log (2 * R + 2) ≤ ((n : ℝ) + 3) * Real.log 2 := by
    calc
      Real.log (2 * R + 2) ≤ Real.log (4 * R) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = ((n : ℝ) + 3) * Real.log 2 := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hR)]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        dsimp only [R]
        rw [Real.log_pow]
        push_cast
        ring
  have hexp : C * (2 * R + 1) * Real.log (2 * R + 2) ≤
      3 * C * R * (((n : ℝ) + 3) * Real.log 2) := by
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left (show 2 * R + 1 ≤ 3 * R by linarith) hC.le)
      hlog (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * R + 2))
      (show 0 ≤ C * (3 * R) by positivity)
    convert hh using 1 <;> ring
  have hsmall : 3 * C * R * ((n : ℝ) + 3) ≤ 6 * C * ((n : ℝ) + 2) * R := by
    have hh := mul_le_mul_of_nonneg_left
      (show 3 * ((n : ℝ) + 3) ≤ 6 * ((n : ℝ) + 2) by linarith [hn])
      (show 0 ≤ C * R by positivity)
    convert hh using 1 <;> ring
  have hBmul : B * Real.log 2 = |Real.log ‖G 0‖| := by
    dsimp [B]
    field_simp
  have hnum : C * (2 * R + 1) * Real.log (2 * R + 2) - Real.log ‖G 0‖ ≤
      (6 * C * ((n : ℝ) + 2) * R + B) * Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hlog2.le
    have hneg : -Real.log ‖G 0‖ ≤ |Real.log ‖G 0‖| := neg_le_abs _
    calc
      C * (2 * R + 1) * Real.log (2 * R + 2) - Real.log ‖G 0‖ ≤
          (3 * C * R * ((n : ℝ) + 3)) * Real.log 2 + |Real.log ‖G 0‖| := by
        nlinarith [hexp, hneg]
      _ ≤ (6 * C * ((n : ℝ) + 2) * R) * Real.log 2 + |Real.log ‖G 0‖| :=
        add_le_add hh le_rfl
      _ = (6 * C * ((n : ℝ) + 2) * R + B) * Real.log 2 := by rw [← hBmul]; ring
  have hscale : 1 ≤ ((n : ℝ) + 2) * R :=
    one_le_mul_of_one_le_of_one_le (by linarith [hn]) hR1
  have hBscale : B ≤ B * (((n : ℝ) + 2) * R) := by
    simpa using mul_le_mul_of_nonneg_left hscale hB
  calc
    (∑' z : ℂ, if ‖z‖ ≤ R then (zeroOrderWeights G z : ℝ) else 0) ≤
        (C * (2 * R + 1) * Real.log (2 * R + 2) - Real.log ‖G 0‖) / Real.log 2 := hj'
    _ ≤ 6 * C * ((n : ℝ) + 2) * R + B := (div_le_iff₀ hlog2).mpr hnum
    _ ≤ (6 * C + B) * (((n : ℝ) + 2) * R) := by nlinarith [hBscale]
    _ ≤ A * (((n : ℝ) + 2) * R) :=
      mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (by positivity)
    _ = A * ((n : ℝ) + 2) * (2 : ℝ) ^ (n + 1) := by dsimp [R]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
