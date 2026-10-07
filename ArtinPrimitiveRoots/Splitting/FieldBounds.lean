import ArtinPrimitiveRoots.Splitting.ZeroFree

/-! `spl:field-bounds`, moved here on 2026-10-07 (statement unchanged): its proof assembles the
compositum and the zero-free descent of `Splitting/ZeroFree.lean`, which imports
`Splitting/Algebraic.lean`, so in `Algebraic.lean` it could never be proved (lane `sol-thin-s7`). -/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- **`spl:field-bounds`**, `07-splitting.tex:19-99`. There are thresholds and constants
depending only on `a` such that, for every sufficiently large prime `q`, the degree and
discriminant estimates and the inherited zero-free region hold. The unramifiedness clause is not
consumed by §7's splitting test. -/
theorem spl_field_bounds (a : ℤ) (ha : 1 < |a|) :
    ∃ qₐ : ℕ, ∃ C : ℝ, 5 ≤ qₐ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q], q.Prime → qₐ ≤ q →
        kummerDegree a q = q * (q - 1) ∧
        absoluteDiscriminant (kummerField a q) ≤
          (q : ℝ) ^ (q * (q - 2)) *
            ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log (absoluteDiscriminant (kummerField a q)) + kummerDegree a q ≤
          C * (kummerDegree a q : ℝ) * Real.log (2 * (q : ℝ)) ∧
        IsGalois ℚ (kummerField a q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * (q : ℤ) →
          (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 (kummerField a q)) = 1) ∧
        ∀ s : ℂ, 1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀ < s.re → s ≠ 1 →
          meromorphicOrderAt (dedekindZetaSharp (kummerField a q)) s ≤ 0 := by
  sorry

end ArtinPrimitiveRoots.Splitting

end
