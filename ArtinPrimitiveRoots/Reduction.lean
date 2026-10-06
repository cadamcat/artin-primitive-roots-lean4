import ArtinPrimitiveRoots.Controlled
import ArtinPrimitiveRoots.Splitting

/-!
# Reduction to controlled predecessors and complete splitting (paper: Theorem `thm:main`)

Source: `01-introduction.tex`, lines 17–26 (statement); `01a-reduction.tex`, lines 98–220 (the
quadratic-nonresidue progression and the proof). Frozen interface: `thm_main`.
-/

namespace ArtinPrimitiveRoots

/-- **Theorem `thm:main`.** For every integer `a` that is neither `-1` nor a square there are
`c_a > 0` and `x_a ≥ 2` such that for every real `x ≥ x_a`, at least `c_a x / (log x)²` primes
`p ∈ (x, 2x)` with `p ∤ a` have `a` as a primitive root. -/
theorem thm_main (a : ℤ) (ha : a ≠ -1) (ha' : ¬ IsSquare a) :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      c * x / Real.log x ^ 2 ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
            orderOf (a : ZMod p) = p - 1} : Set ℕ).ncard : ℝ) := by
  sorry

end ArtinPrimitiveRoots
