import ArtinPrimitiveRoots.TypeII.PD.Physical
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical Filter

private theorem sublinear_power_eventually (C γ r : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) (hr : r < 1) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → C * Real.rpow L r ≤ γ * L := by
  have ht : Tendsto (fun L : ℝ => Real.rpow L (1 - r)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hr)
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop (C / γ))
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hL)
  have hgap := hL₁ L ((le_max_right _ _).trans hL)
  have hprod : Real.rpow L r * Real.rpow L (1 - r) = L := by
    calc
      _ = Real.rpow L (r + (1 - r)) := (Real.rpow_add hLpos _ _).symm
      _ = L := by
        have heq : r + (1 - r) = 1 := by ring
        rw [heq]
        exact Real.rpow_one L
  have hmul : Real.rpow L r * (C / γ) ≤ Real.rpow L r * Real.rpow L (1 - r) :=
    mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hLpos.le r)
  rw [hprod] at hmul
  have h := mul_le_mul_of_nonneg_left hmul hγ.le
  have hcancel : γ * (Real.rpow L r * (C / γ)) = C * Real.rpow L r := by field_simp [hγ.ne']
  rwa [hcancel] at h

/-- Subexponential grid remainders are smaller than every fixed logarithmic power. -/
theorem gridError_logPowerDecay (A B C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L B * Real.exp (C * Real.rpow L (21 / 100 : ℝ) +
        Real.rpow L (9 / 10 : ℝ) - γ * L) ≤ Real.rpow L (-A) := by
  obtain ⟨L₁, hL₁, hFirst⟩ := sublinear_power_eventually C (γ / 4) (21 / 100 : ℝ) hC (by positivity) (by norm_num)
  obtain ⟨L₂, hL₂, hSecond⟩ := sublinear_power_eventually 1 (γ / 4) (9 / 10 : ℝ) (by norm_num) (by positivity) (by norm_num)
  have ht : Tendsto (fun L : ℝ => Real.rpow L (A + B) * Real.exp (-(γ / 2) * L)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A + B) (γ / 2) (by positivity)
  obtain ⟨L₃, hThird⟩ := Filter.eventually_atTop.mp (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let L₀ := max 1 (max L₁ (max L₂ L₃))
  refine ⟨L₀, by simp [L₀], ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) ((by simp [L₀] : 1 ≤ L₀).trans hL)
  have h₁ := hFirst L ((by simp [L₀] : L₁ ≤ L₀).trans hL)
  have h₂ := hSecond L ((by simp [L₀] : L₂ ≤ L₀).trans hL)
  have hsmall := (hThird L ((by simp [L₀] : L₃ ≤ L₀).trans hL)).le
  have hexponent : C * Real.rpow L (21 / 100 : ℝ) + Real.rpow L (9 / 10 : ℝ) - γ * L ≤ -(γ / 2) * L := by
    nlinarith
  have hpow : Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L B := by
    calc
      _ = Real.rpow L (-A + (A + B)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1 <;> ring
  calc
    _ ≤ Real.rpow L B * Real.exp (-(γ / 2) * L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Real.rpow_nonneg hLpos.le B)
    _ = Real.rpow L (-A) * (Real.rpow L (A + B) * Real.exp (-(γ / 2) * L)) := by rw [← hpow]; ring
    _ ≤ Real.rpow L (-A) * 1 := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hLpos.le _)
    _ = _ := mul_one _


/-- Bad-ratio exponential decay dominates every fixed logarithmic power. -/
theorem modelError_logPowerDecay (A B c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L B * Real.exp (-c * Real.rpow L r) ≤ Real.rpow L (-A) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((A + B) / r) c hc).comp
    (tendsto_rpow_atTop hr)
  obtain ⟨L₁, hsmall⟩ := Filter.eventually_atTop.mp
    (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hL)
  have hs := (hsmall L ((le_max_right _ _).trans hL)).le
  have hpow : Real.rpow (Real.rpow L r) ((A + B) / r) = Real.rpow L (A + B) := by
    calc
      _ = Real.rpow L (r * ((A + B) / r)) := (Real.rpow_mul hLpos.le r ((A + B) / r)).symm
      _ = _ := by congr 1; field_simp [hr.ne']
  change Real.rpow (Real.rpow L r) ((A + B) / r) * Real.exp (-c * Real.rpow L r) ≤ 1 at hs
  rw [hpow] at hs
  have hfactor : Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L B := by
    calc
      _ = Real.rpow L (-A + (A + B)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1 <;> ring
  calc
    _ = Real.rpow L (-A) * (Real.rpow L (A + B) * Real.exp (-c * Real.rpow L r)) := by
      rw [← hfactor]; ring
    _ ≤ Real.rpow L (-A) * 1 := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hLpos.le _)
    _ = _ := mul_one _

end ArtinPrimitiveRoots.TypeII.PD
