import Mathlib

/-!
# Buchstab's rough-number densities (paper: (8.x) `eq:rough-density-definition`, Lemma `lem:density`)

Sources: definition `08-type-ii.tex`, lines 254–273; Lemma `lem:density`, `11-sieve.tex`,
lines 146–251.
-/

namespace ArtinPrimitiveRoots.Sieve

open MeasureTheory

/-- The term `D_{γ,j}(w)` of `eq:rough-density-definition`: `D_{γ,1}(w) = 1/w`, and for `j ≥ 2`,
`(1/j!) ∫ 1/(w - ∑_{i<j} t_i) ∏_{i<j} dt_i/t_i` over `t_i ≥ γ` (`1 ≤ i < j`) with
`∑_{i<j} t_i ≤ w - γ`. The index `j = 0` contributes `0`. -/
noncomputable def roughDensityTerm (γ w : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0
  else if j = 1 then 1 / w
  else (1 / (j.factorial : ℝ)) *
    ∫ t : Fin (j - 1) → ℝ,
      Set.indicator {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ}
        (fun t => (1 / (w - ∑ i, t i)) * ∏ i, (1 / t i)) t

/-- `D_γ(w) = ∑_{j ≥ 1} D_{γ,j}(w)` (`eq:rough-density-definition`); for `w > γ > 0` only finitely
many terms are nonzero. -/
noncomputable def roughDensity (γ w : ℝ) : ℝ := ∑' j : ℕ, roughDensityTerm γ w j

/-- **Lemma `lem:density`.** For `0 < b < 1/2`, `∫_b^{1/2} D_t(1 - t) dt/t = D_b(1) - 1`; and there
are absolute constants `b₀, C_d > 0` with `D_b(1) ≤ e^{-γ_E}/b · (1 + C_d e^{-1/(20 b)})` for
`0 < b < b₀` (the paper's `c_d = 1/20`). -/
theorem lem_density :
    (∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1) ∧
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∃ C_d : ℝ, 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        Real.exp (-Real.eulerMascheroniConstant) / b * (1 + C_d * Real.exp (-(1 / 20) / b)) := by
  sorry

end ArtinPrimitiveRoots.Sieve
