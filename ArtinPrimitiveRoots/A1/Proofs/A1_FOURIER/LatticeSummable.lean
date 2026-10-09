import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# A1-FOURIER part `a1_fourier_lattice_summable` (IMPL)

Lattice-point summability for S-integers whose finite components lie in a compact set.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- If the finite components of `m ∈ R` are confined to a compact set `Cf ⊆ ∏_{v∈S_f} F_v`, the
series `∑ (1 + ‖m_∞‖)^{-r}` converges for every `r > [F:ℚ]`.

Proof hint: a compact subset of `F_v` lies in a ball `Theta.ball v (-N)` (compare
`A2_WEIGHTS/Finite.lean` `compact_subset_large_thetaBall`; copy, do not import); hence such `m`
have `v(m) ≤ exp N` at `v ∈ S_f` and are integral outside `S_f`, i.e. lie in the fractional
ideal `J = ∏_{v∈S_f} P_v^{-N}` (a free `ℤ`-module of rank `[F:ℚ]`). Its archimedean image is a
discrete subgroup / `ℤ`-lattice of rank `[F:ℚ]` in `InfinitePlace F → ℂ` (compare
`A1_LATTICE.diagR_isDiscrete`, `NumberField.mixedEmbedding.fractionalIdealLatticeBasis`, and
`archToMixedEquiv D` in `A1_LATTICE/Core.lean`); conclude with
`ZLattice.summable_norm_rpow`/`summable_norm_sub_rpow` and `(1+t)^{-r} ≤ t^{-r}` off `0`.
Used by: `a1_fourier_tensor_majorant`. -/
theorem a1_fourier_lattice_summable (S : SData F CE condη) (D : FieldData F)
    (Cf : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hCf : IsCompact Cf)
    (r : ℝ) (hr : (Module.finrank ℚ F : ℝ) < r) :
    Summable (fun m : S.R =>
      Set.indicator {m : S.R | (S.diag (m : F)).1 ∈ Cf}
        (fun m : S.R => (1 + ‖(S.diag (m : F)).2‖) ^ (-r)) m) := by
  sorry

end ArtinPrimitiveRoots.A1
