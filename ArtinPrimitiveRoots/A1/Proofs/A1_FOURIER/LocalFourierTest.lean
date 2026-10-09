import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs

/-!
# A1-FOURIER part `a1_fourier_local_fourier_test` (IMPL)

The local Fourier transform of a finite test function is again a finite test function.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The local Fourier transform of a locally constant compactly supported function is
continuous, compactly supported and locally constant, for any Haar measure `μ` on `F_v`.

Proof hint: copy (do not import) `A2/Proofs/A2_WEIGHTS/Finite.lean`:
`finiteTest_exists_period_ball` (193), `finiteFourier_hasCompactSupport_of_period` (402),
`finiteFourier_isLocallyConstant` (943). There `finiteFourier v A μ f y = ∫ x, f x * A.ψ v (-(x*y))`
for a `Theta.LocHaar`; here the factors are swapped and `μ` is any Haar measure (nontriviality
of `A.ψ v` comes from `AddCharData` as in those proofs).
Used by: the glue `SData.fourier_isFSTensorSum` (`A1/SLattice.lean`). -/
theorem a1_fourier_local_fourier_test (v : FinPlace F) (A : AddCharData F)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (φ : v.adicCompletion F → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφl : IsLocallyConstant φ) :
    Continuous (a1LocalFourier v A μ φ) ∧ HasCompactSupport (a1LocalFourier v A μ φ) ∧
      IsLocallyConstant (a1LocalFourier v A μ φ) := by
  sorry

end ArtinPrimitiveRoots.A1
