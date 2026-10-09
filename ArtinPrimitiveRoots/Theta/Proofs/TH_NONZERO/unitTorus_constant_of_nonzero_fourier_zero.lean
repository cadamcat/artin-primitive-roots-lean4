import Mathlib.Analysis.Fourier.AddCircleMulti

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A continuous function on a finite-dimensional standard torus is constant
when all its nonzero Fourier coefficients vanish. -/
theorem unitTorus_constant_of_nonzero_fourier_zero
    {d : Type*} [Fintype d] (f : C(UnitAddTorus d, ℂ))
    (h : ∀ n : d → ℤ, n ≠ 0 → UnitAddTorus.mFourierCoeff f n = 0) :
    ∀ x, f x = UnitAddTorus.mFourierCoeff f 0 := by
  have hs : Summable (UnitAddTorus.mFourierCoeff f) :=
    summable_of_ne_finset_zero (s := {0}) (fun n hn => h n (by simpa using hn))
  intro x
  have hsingle := hasSum_single
    (f := fun n : d → ℤ => UnitAddTorus.mFourierCoeff f n • UnitAddTorus.mFourier n x)
    0 (fun n hn => by simp [h n hn])
  have hconstant : HasSum
      (fun n : d → ℤ => UnitAddTorus.mFourierCoeff f n • UnitAddTorus.mFourier n x)
      (UnitAddTorus.mFourierCoeff f 0) := by
    simpa [UnitAddTorus.mFourier_zero] using hsingle
  exact (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs x).unique hconstant

end ArtinPrimitiveRoots.A1.Theta
