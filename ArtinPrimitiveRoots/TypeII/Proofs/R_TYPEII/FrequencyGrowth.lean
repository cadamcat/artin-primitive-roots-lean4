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

/-- A logarithmic power times the proxy's decaying exponential tends to zero.
The bound is stated as `≤ 1` because later frequency estimates multiply it by
fixed powers of `log x`. -/
theorem exists_log_rpow_mul_exp_phase_small
    (r a : ℝ) (_hr : 0 < r) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L a * Real.exp (-L / Real.rpow (Real.log L) r) ≤ 1 := by
  obtain ⟨L₁, hL₁, hlogPow⟩ :=
    log_rpow_le_const_mul_x_rpow (r + 1) (1 / 2) 1
      (by norm_num) (by norm_num)
  have hsqrtLim : Filter.Tendsto (fun L : ℝ => Real.rpow L (1 / 2))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have hsqrtLarge := Filter.eventually_atTop.mp
    (hsqrtLim.eventually_ge_atTop (a + 1))
  obtain ⟨L₂, hL₂⟩ := hsqrtLarge
  let L₀ := max 2 (max L₁ L₂)
  refine ⟨L₀, le_max_left _ _, ?_⟩
  intro L hL
  have hLge2 : 2 ≤ L := (le_max_left 2 (max L₁ L₂)).trans hL
  have hLbase : max L₁ L₂ ≤ L := (le_max_right 2 (max L₁ L₂)).trans hL
  have hLgeL₁ : L₁ ≤ L := (le_max_left L₁ L₂).trans hLbase
  have hLgeL₂ : L₂ ≤ L := (le_max_right L₁ L₂).trans hLbase
  have hLpos : 0 < L := by linarith
  have hlogPos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogNonneg : 0 ≤ Real.log L := le_of_lt hlogPos
  have hsqrt : a + 1 ≤ Real.rpow L (1 / 2) := hL₂ L hLgeL₂
  have hsqrtNonneg : 0 ≤ Real.rpow L (1 / 2) := Real.rpow_nonneg (by linarith) _
  have hsqrtSq : Real.rpow L (1 / 2) * Real.rpow L (1 / 2) = L := by
    change L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L
    rw [← Real.rpow_add (by linarith : 0 < L) (1 / 2) (1 / 2)]
    norm_num
  have hlogPow' : Real.rpow (Real.log L) r * Real.log L ≤ Real.rpow L (1 / 2) := by
    have heq : Real.rpow (Real.log L) (r + 1) =
        Real.rpow (Real.log L) r * Real.log L := by
      change (Real.log L) ^ (r + 1) = (Real.log L) ^ r * Real.log L
      rw [Real.rpow_add_one hlogPos.ne' r]
    rw [← heq]
    simpa using hlogPow L hLgeL₁
  have hfactorNonneg : 0 ≤ Real.rpow (Real.log L) r * Real.log L :=
    mul_nonneg (Real.rpow_nonneg hlogNonneg _) hlogNonneg
  have hprod : (a + 1) * Real.log L * Real.rpow (Real.log L) r ≤ L := by
    calc
      (a + 1) * Real.log L * Real.rpow (Real.log L) r =
          (a + 1) * (Real.rpow (Real.log L) r * Real.log L) := by ring
      _ ≤ Real.rpow L (1 / 2) *
          (Real.rpow (Real.log L) r * Real.log L) :=
        mul_le_mul_of_nonneg_right hsqrt hfactorNonneg
      _ ≤ Real.rpow L (1 / 2) * Real.rpow L (1 / 2) :=
        mul_le_mul_of_nonneg_left hlogPow' hsqrtNonneg
      _ = L := hsqrtSq
  have hden : 0 < Real.rpow (Real.log L) r := Real.rpow_pos_of_pos hlogPos _
  have harg : (a + 1) * Real.log L ≤ L / Real.rpow (Real.log L) r :=
    (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hprod)
  have hexp : Real.exp (-L / Real.rpow (Real.log L) r) ≤
      Real.rpow L (-(a + 1)) := by
    calc
      Real.exp (-L / Real.rpow (Real.log L) r) ≤
          Real.exp (-((a + 1) * Real.log L)) :=
        Real.exp_le_exp.mpr (by simpa [neg_div] using neg_le_neg harg)
      _ = Real.rpow L (-(a + 1)) := by
        change Real.exp (-((a + 1) * Real.log L)) = L ^ (-(a + 1))
        rw [Real.rpow_def_of_pos hLpos (-(a + 1))]
        congr 1
        ring
  have hmul := mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg (by linarith : 0 ≤ L) a)
  calc
    Real.rpow L a * Real.exp (-L / Real.rpow (Real.log L) r) ≤
        Real.rpow L a * Real.rpow L (-(a + 1)) := hmul
    _ = Real.rpow L (-1) := by
      change L ^ a * L ^ (-(a + 1) : ℝ) = L ^ (-1 : ℝ)
      rw [← Real.rpow_add hLpos a (-(a + 1))]
      congr 1
      ring
    _ ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (by linarith : 1 ≤ L) (by norm_num : (-1 : ℝ) ≤ 0)
      simpa using h

end ArtinPrimitiveRoots.Proofs.r_typeii_p
