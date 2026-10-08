import Mathlib

namespace ArtinPrimitiveRoots.Proofs.r_typeii_p

open Filter
open scoped Topology

/-- Any fixed logarithmic power is eventually dominated by a positive power of `x`.
The constants are explicit so frequency arguments can budget their error terms. -/
theorem log_rpow_le_const_mul_x_rpow
    (a b K : ℝ) (hb : 0 < b) (hK : 0 < K) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.rpow (Real.log x) a ≤ K * Real.rpow x b := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) a / Real.rpow x b)
      Filter.atTop (𝓝 0) := by
    exact (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.rpow (Real.log x) a / Real.rpow x b‖ < K := by
    have hball := hlim.eventually
      (Metric.ball_mem_nhds (0 : ℝ) hK)
    filter_upwards [hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x₁ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx₁' : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := (le_max_right x₁ 2).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hden : 0 < Real.rpow x b := Real.rpow_pos_of_pos hxpos _
  have hquot := hx₁ x hx₁'
  have hqnonneg : 0 ≤ Real.rpow (Real.log x) a / Real.rpow x b :=
    div_nonneg (Real.rpow_nonneg hlog _) hden.le
  have hquot' : Real.rpow (Real.log x) a / Real.rpow x b < K := by
    have hquotAbs : |Real.rpow (Real.log x) a / Real.rpow x b| < K := by
      simpa only [Real.norm_eq_abs] using hquot
    have hquotAbsDiv : |Real.rpow (Real.log x) a| / |Real.rpow x b| < K := by
      simpa only [abs_div] using hquotAbs
    have hnum : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog _
    simpa only [abs_of_nonneg hnum, abs_of_pos hden] using hquotAbsDiv
  exact le_of_lt ((div_lt_iff₀ hden).mp hquot')

end ArtinPrimitiveRoots.Proofs.r_typeii_p
