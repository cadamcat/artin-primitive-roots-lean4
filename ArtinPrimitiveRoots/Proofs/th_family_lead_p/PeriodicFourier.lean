import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Classical Pointwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.majorant_sol

variable {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

private theorem periodic_integral_translate
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (Γ : AddSubgroup E) [Countable Γ] (Pd : Set E)
    (hPd : IsAddFundamentalDomain Γ Pd μ)
    (f : E → ℂ) (hf : ∀ a : Γ, ∀ x, f ((a : E) + x) = f x) (y : E) :
    (∫ x in Pd, f (y + x) ∂μ) = ∫ x in Pd, f x ∂μ := by
  have ht : IsAddFundamentalDomain Γ (y +ᵥ Pd) μ := hPd.vadd_of_comm y
  calc
    _ = ∫ x in y +ᵥ Pd, f x ∂μ := by
      convert ((measurePreserving_vadd y μ).setIntegral_image_emb
        (measurableEmbedding_const_vadd y) f Pd).symm using 1
    _ = _ := ht.setIntegral_eq hPd hf

/-- Translating a periodic function multiplies its character integral by the inverse
character value, for any representative fundamental domain. -/
theorem theta_periodic_character_integral_translate
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (Γ : AddSubgroup E) [Countable Γ] (Pd : Set E)
    (hPd : IsAddFundamentalDomain Γ Pd μ)
    (χ : E → ℂ) (hχadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hχper : ∀ a : Γ, χ (a : E) = 1)
    (f : E → ℂ) (hf : ∀ a : Γ, ∀ x, f ((a : E) + x) = f x) (y : E) :
    (∫ x in Pd, f (y + x) * χ x ∂μ) =
      (χ y)⁻¹ * ∫ x in Pd, f x * χ x ∂μ := by
  have hχzero : χ 0 = 1 := by simpa using hχper 0
  have hχne : χ y ≠ 0 := by
    have hinv : χ y * χ (-y) = 1 := by
      rw [← hχadd, add_neg_cancel, hχzero]
    intro hy
    rw [hy, zero_mul] at hinv
    exact zero_ne_one hinv
  let H : E → ℂ := fun x => f x * χ x
  have hH : ∀ a : Γ, ∀ x, H ((a : E) + x) = H x := by
    intro a x
    simp only [H, hf, hχadd, hχper, one_mul]
  have hint : χ y * (∫ x in Pd, f (y + x) * χ x ∂μ) =
      ∫ x in Pd, f x * χ x ∂μ := by
    calc
      _ = ∫ x in Pd, H (y + x) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only [H]
          rw [hχadd]
          ring
      _ = _ := periodic_integral_translate μ Γ Pd hPd H hH y
  calc
    _ = (χ y)⁻¹ * (χ y * (∫ x in Pd, f (y + x) * χ x ∂μ)) := by simp [hχne]
    _ = _ := congrArg (fun z : ℂ => (χ y)⁻¹ * z) hint

end ArtinPrimitiveRoots.Proofs.majorant_sol
