import ArtinPrimitiveRoots.TypeII.Defs

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII

/-- A fixed block length costs less than any positive power at the rough cutoff. -/
theorem fixed_block_cutoff (κ : ℝ) (hκ : 0 < κ) (H : ℕ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (roughCutoff x) ^ (4 * H + 2) ≤ Real.rpow x (κ / 2) := by
  have hκhalf : 0 < κ / 2 := by positivity
  have hL76 : Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) (76 / 100 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 76 / 100)).comp
      Real.tendsto_log_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hL76.eventually_ge_atTop (((4 * H + 2 : ℕ) : ℝ) / (κ / 2)))
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro x hx
  have hx₂ : 2 ≤ x := (le_max_left _ _).trans hx
  have hxT : T ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hfactor : ((4 * H + 2 : ℕ) : ℝ) ≤
      (κ / 2) * Real.rpow (Real.log x) (76 / 100 : ℝ) := by
    have h := (div_le_iff₀ hκhalf).mp (hT x hxT)
    simpa only [mul_comm] using h
  have hsplit : Real.rpow (Real.log x) (76 / 100 : ℝ) *
      Real.rpow (Real.log x) (24 / 100 : ℝ) = Real.log x := by
    change (Real.log x) ^ (76 / 100 : ℝ) *
      (Real.log x) ^ (24 / 100 : ℝ) = Real.log x
    rw [← Real.rpow_add hLpos]
    rw [show (76 / 100 + 24 / 100 : ℝ) = 1 by norm_num]
    exact Real.rpow_one _
  have hExponent : ((4 * H + 2 : ℕ) : ℝ) *
      Real.rpow (Real.log x) (24 / 100 : ℝ) ≤ (κ / 2) * Real.log x := by
    calc
      ((4 * H + 2 : ℕ) : ℝ) * Real.rpow (Real.log x) (24 / 100 : ℝ) ≤
          ((κ / 2) * Real.rpow (Real.log x) (76 / 100 : ℝ)) *
            Real.rpow (Real.log x) (24 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor
          (Real.rpow_nonneg hLpos.le (24 / 100 : ℝ))
      _ = (κ / 2) * Real.log x := by rw [mul_assoc, hsplit]
  calc
    (roughCutoff x) ^ (4 * H + 2) =
        Real.exp (((4 * H + 2 : ℕ) : ℝ) *
          Real.rpow (Real.log x) (24 / 100 : ℝ)) := by
      exact (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((κ / 2) * Real.log x) := Real.exp_le_exp.mpr hExponent
    _ = Real.rpow x (κ / 2) := by
      rw [mul_comm]
      exact (Real.rpow_def_of_pos hxpos (κ / 2)).symm

end ArtinPrimitiveRoots.Proofs.c_bins_sol
