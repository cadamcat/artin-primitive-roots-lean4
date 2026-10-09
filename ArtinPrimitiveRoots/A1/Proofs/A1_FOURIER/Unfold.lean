import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs

/-!
# A1-FOURIER part `a1_fourier_unfold` (IMPL)

Unfolding an integral over `F_S` along a measurable fundamental domain of the diagonal
S-integer lattice.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Unfolding along a fundamental domain `K` of `R ↪ F_S`: for integrable `g`,
`∫ g = ∑_{m ∈ R} ∫_K g(x + m)`, and the series of `∫_K ‖g(x+m)‖` converges.

Proof hint: let `S.R` (additive group, countable since `F` is countable) act on `F_S` by
`m +ᵥ x = S.diag m + x`; the action is measure preserving for the Haar measure `μ`; `hK` and
`hKm` give `IsAddFundamentalDomain S.R K μ` (compare `htoFD` in the proof of the private
`covol_candidate_fundamental_domain_mass_eq`, `A1/SLattice.lean` ~2726–2795); then
`IsAddFundamentalDomain.integral_eq_tsum'` and `lintegral_eq_tsum'` (applied to `‖g‖ₑ`).
Used by: `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_unfold (S : SData F CE condη) {mS : MeasurableSpace S.FS} [BorelSpace S.FS]
    (μ : Measure S.FS) [μ.IsAddHaarMeasure]
    (K : Set S.FS) (hKm : MeasurableSet K)
    (hK : ∀ x : S.FS, ∃! p : S.R × S.FS, p.2 ∈ K ∧ x = S.diag (p.1 : F) + p.2)
    (g : S.FS → ℂ) (hg : Integrable g μ) :
    Summable (fun m : S.R => ∫ x in K, ‖g (x + S.diag (m : F))‖ ∂μ) ∧
      ∫ x, g x ∂μ = ∑' m : S.R, ∫ x in K, g (x + S.diag (m : F)) ∂μ := by
  sorry

end ArtinPrimitiveRoots.A1
