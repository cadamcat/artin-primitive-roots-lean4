import ArtinPrimitiveRoots.A2.Proofs.A2_RF_FORWARD.IntegralSeries

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped Classical ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol

theorem norm_series_integrable_of_integral_norm {α ι : Type}
    [MeasurableSpace α] [Countable ι] (μ : Measure α) (f : ι → α → ℂ)
    (hf : ∀ i, Integrable (f i) μ)
    (hPoint : ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖))
    (hIntegral : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, ‖f i x‖) μ := by
  have hMeas : AEStronglyMeasurable (fun x => ∑' i, ‖f i x‖) μ :=
    AEStronglyMeasurable.tsum (fun i => (hf i).norm.1)
  have hEq : (fun x => ∑' i, ‖f i x‖ₑ) =ᵐ[μ]
      fun x => ‖∑' i, ‖f i x‖‖ₑ := by
    filter_upwards [hPoint] with x hx
    rw [Real.enorm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _)),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hx]
    simp only [ofReal_norm]
  have hEach (i : ι) : (∫⁻ x, ‖f i x‖ₑ ∂μ) =
      ENNReal.ofReal (∫ x, ‖f i x‖ ∂μ) := by
    calc
      _ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
        dsimp [enorm]
        rw [lintegral_coe_eq_integral _ (hf i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
          Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f i x)))]
        simp only [coe_nnnorm]
      _ = _ := Real.enorm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f i x)))
  have hFinite : HasFiniteIntegral (fun x => ∑' i, ‖f i x‖) μ := by
    change (∫⁻ x, ‖∑' i, ‖f i x‖‖ₑ ∂μ) < ∞
    calc
      _ = ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ := lintegral_congr_ae hEq.symm
      _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ := lintegral_tsum (fun i => (hf i).1.enorm)
      _ = ∑' i, ENNReal.ofReal (∫ x, ‖f i x‖ ∂μ) := tsum_congr hEach
      _ < ∞ := hIntegral.tsum_ofReal_lt_top
  exact ⟨hMeas, hFinite⟩

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
