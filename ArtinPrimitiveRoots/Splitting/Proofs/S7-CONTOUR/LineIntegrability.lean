import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Sixth-order decay makes a product with quartic growth integrable. -/
theorem integrable_product_of_growth_decay (L W : ℝ → ℂ)
    (hL : AEStronglyMeasurable L) (hW : AEStronglyMeasurable W)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgrowth : ∀ t : ℝ,
      ‖L t‖ ≤ B * Real.rpow (1 + |t|) (4 : ℝ))
    (hdecay : ∀ t : ℝ,
      ‖W t‖ ≤ C * Real.rpow (1 + |t|) (-6 : ℝ)) :
    Integrable (fun t : ℝ => L t * W t) := by
  have hmajor : Integrable (fun t : ℝ => (B * C) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (B * C)
  apply hmajor.mono' (hL.mul hW)
  apply Filter.Eventually.of_forall
  intro t
  let u : ℝ := 1 + |t|
  have hu : 0 < u := by dsimp [u]; positivity
  have hpow : Real.rpow u (4 : ℝ) * Real.rpow u (-6 : ℝ) =
      Real.rpow u (-2 : ℝ) := by
    calc
      _ = Real.rpow u ((4 : ℝ) + (-6 : ℝ)) := (Real.rpow_add hu _ _).symm
      _ = _ := by norm_num
  have hinv : Real.rpow u (-2 : ℝ) = (u ^ 2)⁻¹ :=
    (Real.rpow_neg hu.le (2 : ℝ)).trans
      (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_two u))
  have hsq : 1 + t ^ 2 ≤ u ^ 2 := by
    dsimp [u]
    nlinarith [abs_nonneg t, sq_abs t]
  have hcompare : (u ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < 1 + t ^ 2) hsq
  calc
    ‖L t * W t‖ = ‖L t‖ * ‖W t‖ := norm_mul _ _
    _ ≤ (B * Real.rpow u (4 : ℝ)) * (C * Real.rpow u (-6 : ℝ)) :=
      mul_le_mul (hgrowth t) (hdecay t) (norm_nonneg _)
        (mul_nonneg hB (Real.rpow_nonneg hu.le _))
    _ = B * C * Real.rpow u (-2 : ℝ) := by
      calc
        _ = B * C * (Real.rpow u (4 : ℝ) * Real.rpow u (-6 : ℝ)) := by ring
        _ = _ := by rw [hpow]
    _ = B * C * (u ^ 2)⁻¹ := by rw [hinv]
    _ ≤ B * C * (1 + t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hcompare (mul_nonneg hB hC)

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
