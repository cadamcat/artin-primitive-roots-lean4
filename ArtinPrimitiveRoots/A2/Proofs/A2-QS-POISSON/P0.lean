import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».Defs

/-!
# A2-QS-POISSON, part P0: smooth cutoffs and the transform `T`

Guide: `runs/lanes/sol-thin-found/PROOFS.md:331-347`.  Hints: smooth bump functions
(`ContDiffBump`, `Real.smoothTransition`); Mellin inversion `mellin_inversion`
(`M/Analysis/MellinInversion.lean`), vertical decay of `Mellin(h)` by repeated integration by
parts in `log x`; Stirling-type bounds for `Gammaℂ` on vertical strips (`|Γ_ℂ(u)/Γ_ℂ(1-u)|` grows
like `|Im u|^{2 Re u - 1}`).  The pole of `Mellin(h)(1-u)` at `u = 1` (from `h(0) ≠ 0`) is
cancelled by the zero of `1/Γ_ℂ(1-u)^{r₂}` (`r₂ ≥ 1` for a totally complex field).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- P0 (IMPL): a cap weight exists (found:331). -/
theorem qs_cap_weight_exists_P0 : ∃ W : ℝ → ℝ, IsCapWeight W := by
  sorry

/-- P0 (IMPL): a dyadic weight exists, and it is a QS weight (found:331-332). -/
theorem qs_dyad_weight_exists_P0 :
    ∃ W : ℝ → ℝ, IsDyadWeight W ∧ IsQSWeight (fun x => (W x : ℂ)) := by
  sorry

/-- P0 (IMPL): Mellin transform of `T h` on the strip `0 < Re u < 1`:
`Mellin(T h)(u) = G_K(u)/G_K(1-u) · Mellin(h)(1-u)` (found:333-334). -/
theorem qs_transform_mellin_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h) (u : ℂ)
    (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    mellin (qsTransform K h) u = qsGammaRatio K u * mellin h (1 - u) := by
  sorry

/-- P0 (IMPL): derivative bounds for `T h` (found:338-343): `≪ x^{-j-η}` on `(0,1]` and
`≪ x^{-A}` on `[1,∞)`, every `A, j` and `η > 0`.  `T h` is smooth on `(0,∞)`. -/
theorem qs_transform_bounds_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h)
    (A j : ℕ) (η : ℝ) (hη : 0 < η) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qsTransform K h) (Set.Ioi 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (x ≤ 1 → ‖iteratedDeriv j (qsTransform K h) x‖ ≤ C * x ^ (-(j : ℝ) - η)) ∧
      (1 ≤ x → ‖iteratedDeriv j (qsTransform K h) x‖ ≤ C * x ^ (-(A : ℝ))) := by
  sorry

/-- P0 (IMPL): half-Mellin preservation (found:344-346): `∫₀^∞ h(t²) dt = ∫₀^∞ (T h)(t²) dt`
(the multiplier is `1` at `u = 1/2`). -/
theorem qs_half_mellin_P0 [IsTotallyComplex K] (h : ℝ → ℂ) (hh : IsQSWeight h) :
    mellin (fun y : ℝ => qsTransform K h (y ^ 2)) 1 = mellin (fun y : ℝ => h (y ^ 2)) 1 := by
  sorry

end ArtinPrimitiveRoots.A2
