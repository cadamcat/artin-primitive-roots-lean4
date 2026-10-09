import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.LatticeSummable

/-!
# A1-FOURIER part `a1_fourier_tensor_majorant` (IMPL)

The explicit summable majorant for lattice translates of a tensor sum, uniform on compacts.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- For a tensor sum `g` and a compact `C ⊆ F_S` there is a summable `b : R → ℝ` with
`‖g(x + m)‖ ≤ b m` for all `m ∈ R`, `x ∈ C`.

Proof hint: reduce to one tensor `(∏ φ_v) ⊗ Φ` (finite sums of majorants). The finite factor is
bounded (continuous, compact support) and vanishes unless `(diag m).1 ∈ Cf := tsupport-product
- (C).1`, compact. Schwartz decay (`SchwartzMap.one_add_le_sup_seminorm_apply` or
`le_seminorm`) gives `‖Φ y‖ ≤ c (1 + ‖y‖)^{-M}`, M = finrank ℚ F + 1; and for `x ∈ C`,
`1 + ‖m_∞‖ ≤ (1 + ‖x_∞‖)(1 + ‖x_∞ + m_∞‖)` (Peetre), so `b m = c' · indicator · (1+‖m_∞‖)^{-M}`,
summable by `a1_fourier_lattice_summable`.
Guide: `runs/lanes/sol-thin-a1/PROOFS.md` 188–190 (explicit majorant).
Uses: `a1_fourier_lattice_summable`. Used by: the glue of `SData.poisson` (`A1/SLattice.lean`). -/
theorem a1_fourier_tensor_majorant (S : SData F CE condη) (D : FieldData F)
    (g : S.FS → ℂ) (hg : S.IsFSTensorSum g) (C : Set S.FS) (hC : IsCompact C) :
    ∃ b : S.R → ℝ, Summable b ∧
      ∀ m : S.R, ∀ x ∈ C, ‖g (x + S.diag (m : F))‖ ≤ b m := by
  sorry

end ArtinPrimitiveRoots.A1
