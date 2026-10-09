import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.EBasic

/-!
# A1-FOURIER part `a1_fourier_orthogonality` (IMPL)

Orthogonality of the characters `x ↦ e(x ν)`, `ν ∈ R`, on a fundamental domain of volume one.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Orthogonality: `∫_K e(x ν) dμ = [ν = 0]` for `ν ∈ R`.

Proof hint: for `ν = 0` the integrand is `1` and `μ K = 1`. For `ν ≠ 0`, `S.diag ν` is a unit of
`F_S` (every component of a nonzero element is nonzero); with `z` from `a1_fourier_e_basic`
put `y = z * (S.diag ν)⁻¹`, so `e(y ν) ≠ 1`. The integrand `h x = e(x ν)` is `R`-periodic by
`hself` and additivity; `K + y` is another fundamental domain, and
`IsAddFundamentalDomain.setIntegral_eq` plus translation invariance of `μ` give
`∫_K h = ∫_K h(x + y) = e(y ν) ∫_K h`, so `∫_K h = 0`. Integrability: `‖h‖ = 1`, `μ K = 1`.
Uses: `a1_fourier_e_basic`. Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_orthogonality (S : SData F CE condη) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (ν : S.R) :
    ∫ x in K, S.e A (x * S.diag (ν : F)) ∂μ = if (ν : F) = 0 then 1 else 0 := by
  sorry

end ArtinPrimitiveRoots.A1
