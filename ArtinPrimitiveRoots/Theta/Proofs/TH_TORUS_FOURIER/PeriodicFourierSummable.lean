import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.ProductFourierDecay
import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.SummableQuadraticProduct

set_option autoImplicit false

open AddCircle
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

/-- A smooth integer-periodic function descends to a continuous torus function
whose Fourier coefficients are summable. -/
theorem periodic_fourier_coeff_summable {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hper : ∀ (x : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ),
      f (x + fun j => (k j : ℝ)) = f x) :
    ∃ F : C(UnitAddTorus (Fin (n + 1)), ℂ),
      (∀ x : Fin (n + 1) → ℝ, F (fun j => (x j : UnitAddCircle)) = f x) ∧
      Summable (UnitAddTorus.mFourierCoeff F) := by
  obtain ⟨F, C, hF, _, hBound⟩ := periodic_fourier_product_decay f hf hper
  refine ⟨F, hF, ?_⟩
  exact ((summable_quadratic_product (n + 1)).mul_left C).of_norm_bounded hBound

end ArtinPrimitiveRoots.Proofs.thsol_torusf
