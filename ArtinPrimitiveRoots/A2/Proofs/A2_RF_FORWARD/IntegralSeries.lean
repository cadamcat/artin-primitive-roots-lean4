import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped Classical ENNReal

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol

theorem integral_tsum_of_norm_sum {α ι : Type} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (f : ι → α → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hSum : ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖))
    (hNorm : Integrable (fun x => ∑' i, ‖f i x‖) μ) :
    Integrable (fun x => ∑' i, f i x) μ ∧
      (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  have hEq : (fun x => ∑' i, ‖f i x‖ₑ) =ᵐ[μ]
      fun x => ‖∑' i, ‖f i x‖‖ₑ := by
    filter_upwards [hSum] with x hx
    rw [Real.enorm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _)),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hx]
    simp only [ofReal_norm]
  have hFinite : (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ) < ∞ := by
    calc
      _ = ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ :=
        (lintegral_tsum (fun i => (hf i).enorm)).symm
      _ = ∫⁻ x, ‖∑' i, ‖f i x‖‖ₑ ∂μ := lintegral_congr_ae hEq
      _ < ∞ := hNorm.2
  have hInt : Integrable (fun x => ∑' i, f i x) μ :=
    hNorm.mono' (AEStronglyMeasurable.tsum hf)
      (hSum.mono (fun x hx => norm_tsum_le_tsum_norm hx))
  exact ⟨hInt, integral_tsum hf hFinite.ne⟩

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
