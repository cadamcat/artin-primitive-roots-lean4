import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FourierCutoff

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- The full density mass controls the main region and its first moment controls the tail. -/
theorem cutoff_density_mass_bounds (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (L A : ℝ) (hL : 0 < L) :
    (∫ u : ℝ in {u | |u| ≤ Real.rpow L A/2}, ‖pd4c_psiHat ψ u‖) ≤
        (∫ u : ℝ, ‖pd4c_psiHat ψ u‖) ∧
    (∫ u : ℝ in {u | |u| ≤ Real.rpow L A/2}ᶜ, ‖pd4c_psiHat ψ u‖) ≤
      2*(∫ u : ℝ, |u| * ‖pd4c_psiHat ψ u‖)*Real.rpow L (-A) := by
  have hP : 0 < Real.rpow L A := Real.rpow_pos_of_pos hL A
  have hnorm : Integrable (fun u : ℝ => ‖pd4c_psiHat ψ u‖) := by
    simpa only [pow_zero, one_mul] using pd4c_psiHat_integrable_pow ψ hψ hcompact 0
  constructor
  · exact setIntegral_le_integral hnorm (Filter.Eventually.of_forall fun u => norm_nonneg _)
  · have hset : {u : ℝ | |u| ≤ Real.rpow L A/2}ᶜ =
        {u : ℝ | Real.rpow L A/2 < |u|} := by
      ext u
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hset]
    have htail := pd4c_psiHat_tail ψ hψ hcompact 1 (Real.rpow L A/2) (by positivity)
    have hneg : Real.rpow L (-A) = (Real.rpow L A)⁻¹ := Real.rpow_neg hL.le A
    calc
      _ ≤ (∫ u : ℝ, |u| * ‖pd4c_psiHat ψ u‖)/(Real.rpow L A/2) := by
        simpa only [pow_one] using htail
      _ = _ := by
        rw [hneg]
        field_simp [hP.ne'] <;> ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
