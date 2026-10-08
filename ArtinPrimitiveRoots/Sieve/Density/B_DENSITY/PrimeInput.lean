import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Arithmetic
import OAI.NumberTheory.PrimeGaps.Main

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open Filter
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

end ArtinPrimitiveRoots.Proofs.b_density_sol
