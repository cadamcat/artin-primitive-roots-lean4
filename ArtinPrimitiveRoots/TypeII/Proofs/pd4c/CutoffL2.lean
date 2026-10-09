import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CutoffIntegral

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical MeasureTheory

noncomputable section

/-- Inner and outer squared matrix bounds pass through a finite Fourier cutoff integral. -/
theorem finite_cutoff_l2_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ℝ → ℂ) (V : ℝ → EuclideanSpace ℂ ι) (f : EuclideanSpace ℂ κ)
    (T : Set ℝ) (hT : MeasurableSet T)
    (hw : Integrable (fun u : ℝ => ‖w u‖))
    (hV : Integrable (fun u : ℝ => w u • V u))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinner : ∀ u ∈ T, (∑ i, ‖V u i‖^2) ≤ a^2*(∑ j, ‖f j‖^2))
    (houter : ∀ u ∉ T, (∑ i, ‖V u i‖^2) ≤ b^2*(∑ j, ‖f j‖^2)) :
    (∑ i, ‖∫ u : ℝ, w u * V u i‖^2) ≤
    ((∫ u : ℝ in T, ‖w u‖)*a + (∫ u : ℝ in Tᶜ, ‖w u‖)*b)^2 *
      (∑ j, ‖f j‖^2) := by
  have hinnerNorm (u : ℝ) (hu : u ∈ T) : ‖V u‖ ≤ a*‖f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg f))).mp
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq] using hinner u hu
  have houterNorm (u : ℝ) (hu : u ∉ T) : ‖V u‖ ≤ b*‖f‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg f))).mp
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq] using houter u hu
  have hnorm := cutoff_integral_norm_bound w V T hT hw a b ‖f‖ hinnerNorm houterNorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have heval (i : ι) : (∫ u : ℝ, w u • V u) i = ∫ u : ℝ, w u * V u i := by
    let P : EuclideanSpace ℂ ι →L[ℂ] ℂ := PiLp.proj 2 (fun _ : ι => ℂ) i
    have h := P.integral_comp_comm hV
    simpa only [P, PiLp.proj_apply, PiLp.smul_apply, smul_eq_mul] using h.symm
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, heval] using hsq

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
