import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.ProductFourierMultiplier

set_option autoImplicit false

open MeasureTheory AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem norm_mFourierCoeff_le_norm {d : Type*} [Fintype d]
    (F : C(UnitAddTorus d, ℂ)) (k : d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff F k‖ ≤ ‖F‖ := by
  have hnorm (z : UnitAddTorus d) : ‖UnitAddTorus.mFourier (-k) z‖ = 1 := by
    simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
      norm_prod, Circle.norm_coe, Finset.prod_const_one]
  have hbound : ∀ᵐ z : UnitAddTorus d, ‖UnitAddTorus.mFourier (-k) z • F z‖ ≤ ‖F‖ := by
    filter_upwards [] with z
    rw [norm_smul, hnorm, one_mul]
    exact F.norm_coe_le_norm z
  simpa only [UnitAddTorus.mFourierCoeff, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const hbound)

/-- Smooth integer-periodic functions have Fourier coefficients bounded by a
constant times the product of inverse quadratic frequency factors. -/
theorem periodic_fourier_product_decay {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ),
      f (x + fun j => (k j : ℝ)) = f x) :
    ∃ (F : C(UnitAddTorus (Fin (n + 1)), ℂ)) (C : ℝ),
      (∀ x : Fin (n + 1) → ℝ, F (fun j => (x j : UnitAddCircle)) = f x) ∧
      0 ≤ C ∧ ∀ k : Fin (n + 1) → ℤ,
        ‖UnitAddTorus.mFourierCoeff F k‖ ≤
          C * ∏ i : Fin (n + 1), (1 + (2 * Real.pi * (k i : ℝ)) ^ 2)⁻¹ := by
  obtain ⟨F, U, hF, hCoeff⟩ := periodic_fourier_product_multiplier f hf hper
  refine ⟨F, ‖U‖, hF, norm_nonneg U, ?_⟩
  intro k
  let p : ℝ := ∏ i : Fin (n + 1), (1 + (2 * Real.pi * (k i : ℝ)) ^ 2)
  have hp : 0 < p := by
    apply Finset.prod_pos
    intro i _
    positivity
  have hCast :
      (∏ i : Fin (n + 1), ((1 + (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ)) =
        (p : ℂ) := by
    simp only [p, Complex.ofReal_prod]
  have hnorm : p * ‖UnitAddTorus.mFourierCoeff F k‖ ≤ ‖U‖ := by
    calc
      p * ‖UnitAddTorus.mFourierCoeff F k‖ =
          ‖UnitAddTorus.mFourierCoeff U k‖ := by
        rw [hCoeff, hCast, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      _ ≤ ‖U‖ := norm_mFourierCoeff_le_norm U k
  have hdiv : ‖UnitAddTorus.mFourierCoeff F k‖ ≤ ‖U‖ / p :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hnorm)
  simpa only [div_eq_mul_inv, p, Finset.prod_inv_distrib] using hdiv

end ArtinPrimitiveRoots.Proofs.thsol_torusf
