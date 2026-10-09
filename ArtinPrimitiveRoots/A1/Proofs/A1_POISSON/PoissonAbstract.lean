import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Unfold
import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Orthogonality
import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Uniqueness

/-!
# A1-POISSON part `a1_fourier_poisson_abstract` (IMPL)

Abstract Poisson summation on `F_S / R` from unfolding, orthogonality and uniqueness.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Abstract Poisson summation for `R ⊂ F_S`: for continuous integrable `f` with a summable
majorant of its `R`-translates, uniform on compacts, and absolutely summable Fourier transform on
`R`, `∑_m f(m) = ∑_ν f̂(ν)` with `f̂(y) = ∫ f(x) e(-x y) dμ` (this is `S.fourier A μ f`).

Proof plan: `P x = ∑' m, f (x + m)` is continuous (local M-test from `hmaj` on compact
neighbourhoods; `F_S` is locally compact) and `R`-periodic (reindex by `Equiv.addLeft`);
`G x = ∑' ν, f̂ ν * e(x ν)` is continuous (M-test with `hdual`, `‖e‖ = 1`) and periodic
(`hself`). Both are bounded (periodic + compact cover `A1_LATTICE.diagR_has_compact_cover`), so
integrable on `K`. Coefficients: `∫_K P e(-xν) = ∑_m ∫_K f(x+m) e(-(x+m)ν) = f̂ ν` by
`integral_tsum` (summability from `a1_fourier_unfold` for `f`), `hself` and `a1_fourier_unfold`
for `f·e(-·ν)`; `∫_K G e(-xν) = f̂ ν` by `integral_tsum` and `a1_fourier_orthogonality`
(for `ν' - ν`). Hence `a1_fourier_uniqueness` gives `P = G`; evaluate at `0`.
Uses: `a1_fourier_e_basic`, `a1_fourier_unfold`, `a1_fourier_orthogonality`,
`a1_fourier_uniqueness`. Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_poisson_abstract (S : SData F CE condη) (D : FieldData F) (A : AddCharData F)
    {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (hKμ : μ K = 1)
    (hself : ∀ r s : S.R, S.e A (S.diag (r : F) * S.diag (s : F)) = 1)
    (hann : ∀ y : S.FS, (∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) →
      ∃ r : S.R, y = S.diag (r : F))
    (f : S.FS → ℂ) (hf : Continuous f) (hfi : Integrable f μ)
    (hmaj : ∀ C : Set S.FS, IsCompact C → ∃ b : S.R → ℝ, Summable b ∧
      ∀ m : S.R, ∀ x ∈ C, ‖f (x + S.diag (m : F))‖ ≤ b m)
    (hdual : Summable (fun ν : S.R => ‖∫ x, f x * S.e A (-(x * S.diag (ν : F))) ∂μ‖)) :
    ∑' m : S.R, f (S.diag (m : F)) =
      ∑' ν : S.R, ∫ x, f x * S.e A (-(x * S.diag (ν : F))) ∂μ := by
  sorry

end ArtinPrimitiveRoots.A1
