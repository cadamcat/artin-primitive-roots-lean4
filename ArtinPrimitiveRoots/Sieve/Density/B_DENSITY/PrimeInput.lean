import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Arithmetic
import OAI.NumberTheory.PrimeGaps.Main

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open MeasureTheory Filter
open scoped Topology

/-- The independent Mangoldt asymptotic used for the density prime input. -/
lemma tendsto_chebyshevPsi_div :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  classical
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    apply MulChar.one_apply
    exact (ZMod.isUnit_iff_coprime n 1).mpr (by simp)
  have herror (x : ℝ) :
      OAI.LargePrimeGaps.primeCharacterError x (1 : DirichletCharacter ℂ 1) =
        ((Chebyshev.psi x - x : ℝ) : ℂ) := by
    simp [OAI.LargePrimeGaps.primeCharacterError,
      OAI.LargePrimeGaps.primeCharacterPrefix, Chebyshev.psi, hχ, Complex.ofReal_sum]
  obtain ⟨M, hM, hbound⟩ := OAI.LargePrimeGaps.primeCharacterError_log_bound
    1 1 (by norm_num) (by norm_num)
  have hevent : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧ (Real.log x) ^ (4 : ℝ) ≤ x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (Real.exp 1),
      OAI.LargePrimeGaps.eventually_log_rpow_le_rpow 4 (by norm_num : (0 : ℝ) < 1)]
      with x hx hex hp
    refine ⟨hx, ?_, ?_⟩
    · rw [← Real.log_exp (1 : ℝ)]
      exact Real.log_le_log (Real.exp_pos 1) hex
    · simpa using hp
  have hMlog : Tendsto (fun x : ℝ => M / Real.log x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul M
  have hupper : ∀ᶠ x : ℝ in atTop, ‖Chebyshev.psi x / x - 1‖ ≤ M / Real.log x := by
    filter_upwards [hevent] with x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hlog : 0 < Real.log x := by linarith [hx.2.1]
    have hb := hbound 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one x hx.1 hx.2.1
      (by convert hx.2.2 using 1 <;> norm_num) (by simpa using hx.2.1)
    rw [herror x] at hb
    simp only [Complex.norm_real, Real.norm_eq_abs] at hb
    have hdiv : Chebyshev.psi x / x - 1 = (Chebyshev.psi x - x) / x := by
      field_simp [hxpos.ne']
    rw [Real.norm_eq_abs, hdiv, abs_div, abs_of_pos hxpos]
    calc
      |Chebyshev.psi x - x| / x ≤
          (M * x * (Real.log x) ^ (-(1 : ℝ))) / x :=
        div_le_div_of_nonneg_right hb hxpos.le
      _ = M / Real.log x := by
        rw [Real.rpow_neg_one]
        field_simp [hxpos.ne', hlog.ne']
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun x : ℝ => norm_nonneg (Chebyshev.psi x / x - 1))
      hupper hMlog)

/-- Prime counting normalized by its asymptotic main term. -/
lemma tendsto_primeCounting_log_div :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
      atTop (𝓝 1) := by
  let R : ℝ → ℝ := fun x => 2 *
    (Real.log x * Real.rpow x ((1 / 2 : ℝ) - 1))
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa [R] using
      (tendsto_log_mul_rpow_sub_one (α := 1 / 2) (by norm_num)).const_mul (2 : ℝ)
  have hupper : ∀ᶠ x : ℝ in atTop,
      ‖(Chebyshev.psi x - Chebyshev.theta x) / x‖ ≤ R x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hxpos]
    calc
      |Chebyshev.psi x - Chebyshev.theta x| / x ≤
          (2 * Real.sqrt x * Real.log x) / x :=
        div_le_div_of_nonneg_right hbound hxpos.le
      _ = R x := by
        dsimp [R]
        have hpow : Real.rpow x ((1 / 2 : ℝ) - 1) = Real.rpow x (1 / 2) / x :=
          Real.rpow_sub_one hxpos.ne' (1 / 2)
        rw [Real.sqrt_eq_rpow x]
        change 2 * Real.rpow x (1 / 2) * Real.log x / x =
          2 * (Real.log x * Real.rpow x ((1 / 2 : ℝ) - 1))
        rw [hpow]
        ring
  have hnorm : Tendsto (fun x : ℝ =>
      ‖(Chebyshev.psi x - Chebyshev.theta x) / x‖) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun x : ℝ =>
      norm_nonneg ((Chebyshev.psi x - Chebyshev.theta x) / x)) hupper hR
  have herror : Tendsto (fun x : ℝ =>
      (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using hnorm
  have htheta : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
    have hsub := tendsto_chebyshevPsi_div.sub herror
    simp only [sub_zero] at hsub
    apply hsub.congr'
    filter_upwards [] with x
    ring
  let I : ℝ → ℝ := fun x =>
    ∫ t in 2..x, Chebyshev.theta t / (t * Real.log t ^ 2)
  have hI : Tendsto (fun x : ℝ => I x / (x / Real.log x)) atTop (𝓝 0) := by
    simpa [I] using Chebyshev.integral_theta_div_log_sq_isLittleO.tendsto_div_nhds_zero
  have hsum := htheta.add hI
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hpi : (Nat.primeCounting ⌊x⌋₊ : ℝ) = Chebyshev.theta x / Real.log x + I x :=
    Chebyshev.primeCounting_eq_theta_div_log_add_integral hx
  rw [hpi]
  field_simp [hxpos.ne', hlogpos.ne']
  <;> ring

end ArtinPrimitiveRoots.Proofs.b_density_sol
